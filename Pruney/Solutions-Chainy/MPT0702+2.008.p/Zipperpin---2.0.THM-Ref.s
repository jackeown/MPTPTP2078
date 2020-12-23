%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0dRIWVYpFZ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:43 EST 2020

% Result     : Theorem 25.89s
% Output     : Refutation 25.99s
% Verified   : 
% Statistics : Number of formulae       :  246 (1175 expanded)
%              Number of leaves         :   43 ( 382 expanded)
%              Depth                    :   32
%              Number of atoms          : 1971 (11009 expanded)
%              Number of equality atoms :  149 ( 770 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ ( k6_subset_1 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) )
      | ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ X0 )
      = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ ( k6_subset_1 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_xboole_0 @ X30 @ X31 )
        = X30 )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k6_subset_1 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','41'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('43',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_funct_1 @ X52 )
      | ( ( k9_relat_1 @ X52 @ ( k3_xboole_0 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X52 @ X53 ) @ ( k9_relat_1 @ X52 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('44',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_funct_1 @ X52 )
      | ( ( k9_relat_1 @ X52 @ ( k3_xboole_0 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X52 @ X53 ) @ ( k9_relat_1 @ X52 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('45',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_xboole_0 @ X30 @ X31 )
        = X30 )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) )
    = ( k9_relat_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = ( k9_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k9_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_funct_1 @ X52 )
      | ( ( k9_relat_1 @ X52 @ ( k3_xboole_0 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X52 @ X53 ) @ ( k9_relat_1 @ X52 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
        = ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['43','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
      = ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( k9_relat_1 @ sk_C_1 @ k1_xboole_0 )
    = ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('67',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('72',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X32 @ X33 ) @ X32 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','75'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('77',plain,(
    ! [X41: $i] :
      ( r1_xboole_0 @ X41 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('82',plain,(
    ! [X34: $i] :
      ( ( k4_xboole_0 @ X34 @ k1_xboole_0 )
      = X34 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('84',plain,(
    ! [X34: $i] :
      ( ( k6_subset_1 @ X34 @ k1_xboole_0 )
      = X34 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('87',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k10_relat_1 @ X55 @ ( k6_subset_1 @ X56 @ X57 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X55 @ X56 ) @ ( k10_relat_1 @ X55 @ X57 ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('88',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k10_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','92'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('94',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X58 @ ( k10_relat_1 @ X58 @ X59 ) ) @ X59 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('100',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('103',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k9_relat_1 @ sk_C_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','105'])).

thf('107',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ ( k6_subset_1 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('109',plain,(
    ! [X42: $i,X43: $i] :
      ( r1_tarski @ X42 @ ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('110',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('111',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_xboole_0 @ X29 @ X28 )
        = X28 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('113',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['108','115'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('117',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      | ~ ( r1_tarski @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('118',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('119',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X36 @ X37 ) @ X38 )
      | ~ ( r1_tarski @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['107','120'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('122',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r1_tarski @ X60 @ ( k1_relat_1 @ X61 ) )
      | ( r1_tarski @ X60 @ ( k10_relat_1 @ X61 @ ( k9_relat_1 @ X61 @ X60 ) ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','125'])).

thf('127',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('128',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('129',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('130',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k6_subset_1 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = ( k5_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('138',plain,
    ( ( k9_relat_1 @ sk_C_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X58 @ ( k10_relat_1 @ X58 @ X59 ) ) @ X59 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('142',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( k1_xboole_0
      = ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('146',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X32 @ X33 ) @ X32 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['144','147','148','149','150','151'])).

thf('153',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_funct_1 @ X52 )
      | ( ( k9_relat_1 @ X52 @ ( k3_xboole_0 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X52 @ X53 ) @ ( k9_relat_1 @ X52 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('156',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','155','156','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('161',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ) @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('162',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) )
      = ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['161','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) )
    = ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ) @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = ( k5_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('174',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['172','177'])).

thf('179',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['171','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( k10_relat_1 @ sk_C_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['170','182'])).

thf('184',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['126','183'])).

thf('185',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('186',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('188',plain,
    ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ ( k6_subset_1 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('191',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('193',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('195',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ( ( k4_xboole_0 @ X20 @ X21 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('197',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('198',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ( ( k6_subset_1 @ X20 @ X21 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['195','198'])).

thf('200',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    $false ),
    inference(demod,[status(thm)],['0','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0dRIWVYpFZ
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 25.89/26.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 25.89/26.16  % Solved by: fo/fo7.sh
% 25.89/26.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.89/26.16  % done 22440 iterations in 25.707s
% 25.89/26.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 25.89/26.16  % SZS output start Refutation
% 25.89/26.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 25.89/26.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 25.89/26.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 25.89/26.16  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 25.89/26.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 25.89/26.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 25.89/26.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 25.89/26.16  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 25.89/26.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 25.89/26.16  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 25.89/26.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 25.89/26.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 25.89/26.16  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 25.89/26.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 25.89/26.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 25.89/26.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 25.89/26.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 25.89/26.16  thf(sk_A_type, type, sk_A: $i).
% 25.89/26.16  thf(sk_B_type, type, sk_B: $i).
% 25.89/26.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 25.89/26.16  thf(t157_funct_1, conjecture,
% 25.89/26.16    (![A:$i,B:$i,C:$i]:
% 25.89/26.16     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 25.89/26.16       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 25.89/26.16           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 25.89/26.16         ( r1_tarski @ A @ B ) ) ))).
% 25.89/26.16  thf(zf_stmt_0, negated_conjecture,
% 25.89/26.16    (~( ![A:$i,B:$i,C:$i]:
% 25.89/26.16        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 25.89/26.16          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 25.89/26.16              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 25.89/26.16            ( r1_tarski @ A @ B ) ) ) )),
% 25.89/26.16    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 25.89/26.16  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 25.89/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.89/26.16  thf(t48_xboole_1, axiom,
% 25.89/26.16    (![A:$i,B:$i]:
% 25.89/26.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 25.89/26.16  thf('1', plain,
% 25.89/26.16      (![X39 : $i, X40 : $i]:
% 25.89/26.16         ((k4_xboole_0 @ X39 @ (k4_xboole_0 @ X39 @ X40))
% 25.89/26.16           = (k3_xboole_0 @ X39 @ X40))),
% 25.89/26.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.89/26.16  thf(redefinition_k6_subset_1, axiom,
% 25.89/26.16    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 25.89/26.16  thf('2', plain,
% 25.89/26.16      (![X44 : $i, X45 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.89/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.89/26.16  thf('3', plain,
% 25.89/26.16      (![X44 : $i, X45 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.89/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.89/26.16  thf('4', plain,
% 25.89/26.16      (![X39 : $i, X40 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X39 @ (k6_subset_1 @ X39 @ X40))
% 25.89/26.16           = (k3_xboole_0 @ X39 @ X40))),
% 25.89/26.16      inference('demod', [status(thm)], ['1', '2', '3'])).
% 25.89/26.16  thf(d5_xboole_0, axiom,
% 25.89/26.16    (![A:$i,B:$i,C:$i]:
% 25.89/26.16     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 25.89/26.16       ( ![D:$i]:
% 25.89/26.16         ( ( r2_hidden @ D @ C ) <=>
% 25.89/26.16           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 25.89/26.16  thf('5', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.89/26.16         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 25.89/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 25.89/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.89/26.16      inference('cnf', [status(esa)], [d5_xboole_0])).
% 25.89/26.16  thf('6', plain,
% 25.89/26.16      (![X44 : $i, X45 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.89/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.89/26.16  thf('7', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.89/26.16         (((X11) = (k6_subset_1 @ X7 @ X8))
% 25.89/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 25.89/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.89/26.16      inference('demod', [status(thm)], ['5', '6'])).
% 25.89/26.16  thf('8', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 25.89/26.16          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 25.89/26.16      inference('eq_fact', [status(thm)], ['7'])).
% 25.89/26.16  thf('9', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.89/26.16         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 25.89/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 25.89/26.16          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 25.89/26.16          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.89/26.16      inference('cnf', [status(esa)], [d5_xboole_0])).
% 25.89/26.16  thf('10', plain,
% 25.89/26.16      (![X44 : $i, X45 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.89/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.89/26.16  thf('11', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.89/26.16         (((X11) = (k6_subset_1 @ X7 @ X8))
% 25.89/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 25.89/26.16          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 25.89/26.16          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.89/26.16      inference('demod', [status(thm)], ['9', '10'])).
% 25.89/26.16  thf('12', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         (((X0) = (k6_subset_1 @ X0 @ X1))
% 25.89/26.16          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 25.89/26.16          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 25.89/26.16          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 25.89/26.16      inference('sup-', [status(thm)], ['8', '11'])).
% 25.89/26.16  thf('13', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 25.89/26.16          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 25.89/26.16          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 25.89/26.16      inference('simplify', [status(thm)], ['12'])).
% 25.89/26.16  thf('14', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 25.89/26.16          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 25.89/26.16      inference('eq_fact', [status(thm)], ['7'])).
% 25.89/26.16  thf('15', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         (((X0) = (k6_subset_1 @ X0 @ X1))
% 25.89/26.16          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 25.89/26.16      inference('clc', [status(thm)], ['13', '14'])).
% 25.89/26.16  thf('16', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 25.89/26.16          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 25.89/26.16      inference('eq_fact', [status(thm)], ['7'])).
% 25.89/26.16  thf('17', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 25.89/26.16         (~ (r2_hidden @ X10 @ X9)
% 25.89/26.16          | ~ (r2_hidden @ X10 @ X8)
% 25.89/26.16          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 25.89/26.16      inference('cnf', [status(esa)], [d5_xboole_0])).
% 25.89/26.16  thf('18', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X10 : $i]:
% 25.89/26.16         (~ (r2_hidden @ X10 @ X8)
% 25.89/26.16          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 25.89/26.16      inference('simplify', [status(thm)], ['17'])).
% 25.89/26.16  thf('19', plain,
% 25.89/26.16      (![X44 : $i, X45 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.89/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.89/26.16  thf('20', plain,
% 25.89/26.16      (![X7 : $i, X8 : $i, X10 : $i]:
% 25.89/26.16         (~ (r2_hidden @ X10 @ X8)
% 25.89/26.16          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 25.89/26.16      inference('demod', [status(thm)], ['18', '19'])).
% 25.89/26.16  thf('21', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.89/26.16         (((k6_subset_1 @ X1 @ X0)
% 25.89/26.16            = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X2))
% 25.89/26.16          | ~ (r2_hidden @ 
% 25.89/26.16               (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 25.89/26.16               X0))),
% 25.89/26.16      inference('sup-', [status(thm)], ['16', '20'])).
% 25.89/26.16  thf('22', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         (((k6_subset_1 @ X1 @ X0)
% 25.89/26.16            = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0))
% 25.89/26.16          | ((k6_subset_1 @ X1 @ X0)
% 25.89/26.16              = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0)))),
% 25.89/26.16      inference('sup-', [status(thm)], ['15', '21'])).
% 25.89/26.16  thf('23', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X1 @ X0)
% 25.89/26.16           = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 25.89/26.16      inference('simplify', [status(thm)], ['22'])).
% 25.89/26.16  thf('24', plain,
% 25.89/26.16      (![X39 : $i, X40 : $i]:
% 25.89/26.16         ((k6_subset_1 @ X39 @ (k6_subset_1 @ X39 @ X40))
% 25.89/26.16           = (k3_xboole_0 @ X39 @ X40))),
% 25.89/26.16      inference('demod', [status(thm)], ['1', '2', '3'])).
% 25.89/26.16  thf('25', plain,
% 25.89/26.16      (![X0 : $i, X1 : $i]:
% 25.89/26.16         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0))
% 25.89/26.16           = (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 25.89/26.16      inference('sup+', [status(thm)], ['23', '24'])).
% 25.89/26.16  thf(d10_xboole_0, axiom,
% 25.89/26.16    (![A:$i,B:$i]:
% 25.89/26.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 25.89/26.16  thf('26', plain,
% 25.89/26.16      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 25.99/26.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.99/26.16  thf('27', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 25.99/26.16      inference('simplify', [status(thm)], ['26'])).
% 25.99/26.16  thf(t28_xboole_1, axiom,
% 25.99/26.16    (![A:$i,B:$i]:
% 25.99/26.16     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 25.99/26.16  thf('28', plain,
% 25.99/26.16      (![X30 : $i, X31 : $i]:
% 25.99/26.16         (((k3_xboole_0 @ X30 @ X31) = (X30)) | ~ (r1_tarski @ X30 @ X31))),
% 25.99/26.16      inference('cnf', [status(esa)], [t28_xboole_1])).
% 25.99/26.16  thf('29', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['27', '28'])).
% 25.99/26.16  thf(t100_xboole_1, axiom,
% 25.99/26.16    (![A:$i,B:$i]:
% 25.99/26.16     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 25.99/26.16  thf('30', plain,
% 25.99/26.16      (![X23 : $i, X24 : $i]:
% 25.99/26.16         ((k4_xboole_0 @ X23 @ X24)
% 25.99/26.16           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 25.99/26.16      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.99/26.16  thf('31', plain,
% 25.99/26.16      (![X44 : $i, X45 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.16  thf('32', plain,
% 25.99/26.16      (![X23 : $i, X24 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X23 @ X24)
% 25.99/26.16           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 25.99/26.16      inference('demod', [status(thm)], ['30', '31'])).
% 25.99/26.16  thf('33', plain,
% 25.99/26.16      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 25.99/26.16      inference('sup+', [status(thm)], ['29', '32'])).
% 25.99/26.16  thf('34', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 25.99/26.16      inference('simplify', [status(thm)], ['26'])).
% 25.99/26.16  thf(l32_xboole_1, axiom,
% 25.99/26.16    (![A:$i,B:$i]:
% 25.99/26.16     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 25.99/26.16  thf('35', plain,
% 25.99/26.16      (![X20 : $i, X22 : $i]:
% 25.99/26.16         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 25.99/26.16          | ~ (r1_tarski @ X20 @ X22))),
% 25.99/26.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 25.99/26.16  thf('36', plain,
% 25.99/26.16      (![X44 : $i, X45 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.16  thf('37', plain,
% 25.99/26.16      (![X20 : $i, X22 : $i]:
% 25.99/26.16         (((k6_subset_1 @ X20 @ X22) = (k1_xboole_0))
% 25.99/26.16          | ~ (r1_tarski @ X20 @ X22))),
% 25.99/26.16      inference('demod', [status(thm)], ['35', '36'])).
% 25.99/26.16  thf('38', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['34', '37'])).
% 25.99/26.16  thf('39', plain,
% 25.99/26.16      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 25.99/26.16      inference('sup+', [status(thm)], ['29', '32'])).
% 25.99/26.16  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.16      inference('demod', [status(thm)], ['38', '39'])).
% 25.99/26.16  thf('41', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         ((k1_xboole_0) = (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 25.99/26.16      inference('demod', [status(thm)], ['25', '33', '40'])).
% 25.99/26.16  thf('42', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         ((k1_xboole_0)
% 25.99/26.16           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 25.99/26.16      inference('sup+', [status(thm)], ['4', '41'])).
% 25.99/26.16  thf(t121_funct_1, axiom,
% 25.99/26.16    (![A:$i,B:$i,C:$i]:
% 25.99/26.16     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 25.99/26.16       ( ( v2_funct_1 @ C ) =>
% 25.99/26.16         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 25.99/26.16           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 25.99/26.16  thf('43', plain,
% 25.99/26.16      (![X52 : $i, X53 : $i, X54 : $i]:
% 25.99/26.16         (~ (v2_funct_1 @ X52)
% 25.99/26.16          | ((k9_relat_1 @ X52 @ (k3_xboole_0 @ X53 @ X54))
% 25.99/26.16              = (k3_xboole_0 @ (k9_relat_1 @ X52 @ X53) @ 
% 25.99/26.16                 (k9_relat_1 @ X52 @ X54)))
% 25.99/26.16          | ~ (v1_funct_1 @ X52)
% 25.99/26.16          | ~ (v1_relat_1 @ X52))),
% 25.99/26.16      inference('cnf', [status(esa)], [t121_funct_1])).
% 25.99/26.16  thf('44', plain,
% 25.99/26.16      (![X52 : $i, X53 : $i, X54 : $i]:
% 25.99/26.16         (~ (v2_funct_1 @ X52)
% 25.99/26.16          | ((k9_relat_1 @ X52 @ (k3_xboole_0 @ X53 @ X54))
% 25.99/26.16              = (k3_xboole_0 @ (k9_relat_1 @ X52 @ X53) @ 
% 25.99/26.16                 (k9_relat_1 @ X52 @ X54)))
% 25.99/26.16          | ~ (v1_funct_1 @ X52)
% 25.99/26.16          | ~ (v1_relat_1 @ X52))),
% 25.99/26.16      inference('cnf', [status(esa)], [t121_funct_1])).
% 25.99/26.16  thf('45', plain,
% 25.99/26.16      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_C_1 @ sk_B))),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('46', plain,
% 25.99/26.16      (![X30 : $i, X31 : $i]:
% 25.99/26.16         (((k3_xboole_0 @ X30 @ X31) = (X30)) | ~ (r1_tarski @ X30 @ X31))),
% 25.99/26.16      inference('cnf', [status(esa)], [t28_xboole_1])).
% 25.99/26.16  thf('47', plain,
% 25.99/26.16      (((k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 25.99/26.16         (k9_relat_1 @ sk_C_1 @ sk_B)) = (k9_relat_1 @ sk_C_1 @ sk_A))),
% 25.99/26.16      inference('sup-', [status(thm)], ['45', '46'])).
% 25.99/26.16  thf('48', plain,
% 25.99/26.16      ((((k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.99/26.16          = (k9_relat_1 @ sk_C_1 @ sk_A))
% 25.99/26.16        | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.16        | ~ (v1_funct_1 @ sk_C_1)
% 25.99/26.16        | ~ (v2_funct_1 @ sk_C_1))),
% 25.99/26.16      inference('sup+', [status(thm)], ['44', '47'])).
% 25.99/26.16  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('51', plain, ((v2_funct_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('52', plain,
% 25.99/26.16      (((k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.99/26.16         = (k9_relat_1 @ sk_C_1 @ sk_A))),
% 25.99/26.16      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 25.99/26.16  thf('53', plain,
% 25.99/26.16      (![X52 : $i, X53 : $i, X54 : $i]:
% 25.99/26.16         (~ (v2_funct_1 @ X52)
% 25.99/26.16          | ((k9_relat_1 @ X52 @ (k3_xboole_0 @ X53 @ X54))
% 25.99/26.16              = (k3_xboole_0 @ (k9_relat_1 @ X52 @ X53) @ 
% 25.99/26.16                 (k9_relat_1 @ X52 @ X54)))
% 25.99/26.16          | ~ (v1_funct_1 @ X52)
% 25.99/26.16          | ~ (v1_relat_1 @ X52))),
% 25.99/26.16      inference('cnf', [status(esa)], [t121_funct_1])).
% 25.99/26.16  thf('54', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         (((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.16            (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))
% 25.99/26.16            = (k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 25.99/26.16               (k9_relat_1 @ sk_C_1 @ X0)))
% 25.99/26.16          | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.16          | ~ (v1_funct_1 @ sk_C_1)
% 25.99/26.16          | ~ (v2_funct_1 @ sk_C_1))),
% 25.99/26.16      inference('sup+', [status(thm)], ['52', '53'])).
% 25.99/26.16  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('56', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('57', plain, ((v2_funct_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('58', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         ((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.16           (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))
% 25.99/26.16           = (k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 25.99/26.16              (k9_relat_1 @ sk_C_1 @ X0)))),
% 25.99/26.16      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 25.99/26.16  thf('59', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         (((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.16            (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))
% 25.99/26.16            = (k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0)))
% 25.99/26.16          | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.16          | ~ (v1_funct_1 @ sk_C_1)
% 25.99/26.16          | ~ (v2_funct_1 @ sk_C_1))),
% 25.99/26.16      inference('sup+', [status(thm)], ['43', '58'])).
% 25.99/26.16  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('62', plain, ((v2_funct_1 @ sk_C_1)),
% 25.99/26.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.16  thf('63', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         ((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.16           (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))
% 25.99/26.16           = (k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 25.99/26.16      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 25.99/26.16  thf('64', plain,
% 25.99/26.16      (((k9_relat_1 @ sk_C_1 @ k1_xboole_0)
% 25.99/26.16         = (k9_relat_1 @ sk_C_1 @ 
% 25.99/26.16            (k3_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B))))),
% 25.99/26.16      inference('sup+', [status(thm)], ['42', '63'])).
% 25.99/26.16  thf('65', plain,
% 25.99/26.16      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.99/26.16         (((X11) = (k6_subset_1 @ X7 @ X8))
% 25.99/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 25.99/26.16          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.99/26.16      inference('demod', [status(thm)], ['5', '6'])).
% 25.99/26.16  thf('66', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['34', '37'])).
% 25.99/26.16  thf('67', plain,
% 25.99/26.16      (![X7 : $i, X8 : $i, X10 : $i]:
% 25.99/26.16         (~ (r2_hidden @ X10 @ X8)
% 25.99/26.16          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 25.99/26.16      inference('demod', [status(thm)], ['18', '19'])).
% 25.99/26.16  thf('68', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['66', '67'])).
% 25.99/26.16  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 25.99/26.16      inference('condensation', [status(thm)], ['68'])).
% 25.99/26.16  thf('70', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 25.99/26.16          | ((X1) = (k6_subset_1 @ k1_xboole_0 @ X0)))),
% 25.99/26.16      inference('sup-', [status(thm)], ['65', '69'])).
% 25.99/26.16  thf(t36_xboole_1, axiom,
% 25.99/26.16    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 25.99/26.16  thf('71', plain,
% 25.99/26.16      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 25.99/26.16      inference('cnf', [status(esa)], [t36_xboole_1])).
% 25.99/26.16  thf('72', plain,
% 25.99/26.16      (![X44 : $i, X45 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.16  thf('73', plain,
% 25.99/26.16      (![X32 : $i, X33 : $i]: (r1_tarski @ (k6_subset_1 @ X32 @ X33) @ X32)),
% 25.99/26.16      inference('demod', [status(thm)], ['71', '72'])).
% 25.99/26.16  thf(t3_xboole_1, axiom,
% 25.99/26.16    (![A:$i]:
% 25.99/26.16     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 25.99/26.16  thf('74', plain,
% 25.99/26.16      (![X35 : $i]:
% 25.99/26.16         (((X35) = (k1_xboole_0)) | ~ (r1_tarski @ X35 @ k1_xboole_0))),
% 25.99/26.16      inference('cnf', [status(esa)], [t3_xboole_1])).
% 25.99/26.16  thf('75', plain,
% 25.99/26.16      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['73', '74'])).
% 25.99/26.16  thf('76', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 25.99/26.16          | ((X1) = (k1_xboole_0)))),
% 25.99/26.16      inference('demod', [status(thm)], ['70', '75'])).
% 25.99/26.16  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 25.99/26.16  thf('77', plain, (![X41 : $i]: (r1_xboole_0 @ X41 @ k1_xboole_0)),
% 25.99/26.16      inference('cnf', [status(esa)], [t65_xboole_1])).
% 25.99/26.16  thf(d7_xboole_0, axiom,
% 25.99/26.16    (![A:$i,B:$i]:
% 25.99/26.16     ( ( r1_xboole_0 @ A @ B ) <=>
% 25.99/26.16       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 25.99/26.16  thf('78', plain,
% 25.99/26.16      (![X12 : $i, X13 : $i]:
% 25.99/26.16         (((k3_xboole_0 @ X12 @ X13) = (k1_xboole_0))
% 25.99/26.16          | ~ (r1_xboole_0 @ X12 @ X13))),
% 25.99/26.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 25.99/26.16  thf('79', plain,
% 25.99/26.16      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['77', '78'])).
% 25.99/26.16  thf('80', plain,
% 25.99/26.16      (![X23 : $i, X24 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X23 @ X24)
% 25.99/26.16           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 25.99/26.16      inference('demod', [status(thm)], ['30', '31'])).
% 25.99/26.16  thf('81', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 25.99/26.16      inference('sup+', [status(thm)], ['79', '80'])).
% 25.99/26.16  thf(t3_boole, axiom,
% 25.99/26.16    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 25.99/26.16  thf('82', plain, (![X34 : $i]: ((k4_xboole_0 @ X34 @ k1_xboole_0) = (X34))),
% 25.99/26.16      inference('cnf', [status(esa)], [t3_boole])).
% 25.99/26.16  thf('83', plain,
% 25.99/26.16      (![X44 : $i, X45 : $i]:
% 25.99/26.16         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.16  thf('84', plain, (![X34 : $i]: ((k6_subset_1 @ X34 @ k1_xboole_0) = (X34))),
% 25.99/26.16      inference('demod', [status(thm)], ['82', '83'])).
% 25.99/26.16  thf('85', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 25.99/26.16      inference('sup+', [status(thm)], ['81', '84'])).
% 25.99/26.16  thf('86', plain,
% 25.99/26.16      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 25.99/26.16      inference('sup+', [status(thm)], ['29', '32'])).
% 25.99/26.16  thf(t138_funct_1, axiom,
% 25.99/26.16    (![A:$i,B:$i,C:$i]:
% 25.99/26.16     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 25.99/26.16       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 25.99/26.16         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 25.99/26.16  thf('87', plain,
% 25.99/26.16      (![X55 : $i, X56 : $i, X57 : $i]:
% 25.99/26.16         (((k10_relat_1 @ X55 @ (k6_subset_1 @ X56 @ X57))
% 25.99/26.16            = (k6_subset_1 @ (k10_relat_1 @ X55 @ X56) @ 
% 25.99/26.16               (k10_relat_1 @ X55 @ X57)))
% 25.99/26.16          | ~ (v1_funct_1 @ X55)
% 25.99/26.16          | ~ (v1_relat_1 @ X55))),
% 25.99/26.16      inference('cnf', [status(esa)], [t138_funct_1])).
% 25.99/26.16  thf('88', plain,
% 25.99/26.16      (![X7 : $i, X8 : $i, X10 : $i]:
% 25.99/26.16         (~ (r2_hidden @ X10 @ X8)
% 25.99/26.16          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 25.99/26.16      inference('demod', [status(thm)], ['18', '19'])).
% 25.99/26.16  thf('89', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.99/26.16         (~ (r2_hidden @ X3 @ (k10_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)))
% 25.99/26.16          | ~ (v1_relat_1 @ X2)
% 25.99/26.16          | ~ (v1_funct_1 @ X2)
% 25.99/26.16          | ~ (r2_hidden @ X3 @ (k10_relat_1 @ X2 @ X0)))),
% 25.99/26.16      inference('sup-', [status(thm)], ['87', '88'])).
% 25.99/26.16  thf('90', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.99/26.16         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 25.99/26.16          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ X0))
% 25.99/26.16          | ~ (v1_funct_1 @ X1)
% 25.99/26.16          | ~ (v1_relat_1 @ X1))),
% 25.99/26.16      inference('sup-', [status(thm)], ['86', '89'])).
% 25.99/26.16  thf('91', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         (~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 25.99/26.16          | ~ (v1_relat_1 @ X0)
% 25.99/26.16          | ~ (v1_funct_1 @ X0)
% 25.99/26.16          | ~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 25.99/26.16      inference('sup-', [status(thm)], ['85', '90'])).
% 25.99/26.16  thf('92', plain,
% 25.99/26.16      (![X0 : $i, X1 : $i]:
% 25.99/26.16         (~ (v1_funct_1 @ X0)
% 25.99/26.16          | ~ (v1_relat_1 @ X0)
% 25.99/26.16          | ~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 25.99/26.16      inference('simplify', [status(thm)], ['91'])).
% 25.99/26.16  thf('93', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 25.99/26.16          | ~ (v1_relat_1 @ X0)
% 25.99/26.16          | ~ (v1_funct_1 @ X0))),
% 25.99/26.16      inference('sup-', [status(thm)], ['76', '92'])).
% 25.99/26.16  thf(t145_funct_1, axiom,
% 25.99/26.16    (![A:$i,B:$i]:
% 25.99/26.16     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.99/26.16       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 25.99/26.16  thf('94', plain,
% 25.99/26.16      (![X58 : $i, X59 : $i]:
% 25.99/26.16         ((r1_tarski @ (k9_relat_1 @ X58 @ (k10_relat_1 @ X58 @ X59)) @ X59)
% 25.99/26.16          | ~ (v1_funct_1 @ X58)
% 25.99/26.16          | ~ (v1_relat_1 @ X58))),
% 25.99/26.16      inference('cnf', [status(esa)], [t145_funct_1])).
% 25.99/26.16  thf('95', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         ((r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 25.99/26.16          | ~ (v1_funct_1 @ X0)
% 25.99/26.16          | ~ (v1_relat_1 @ X0)
% 25.99/26.16          | ~ (v1_relat_1 @ X0)
% 25.99/26.16          | ~ (v1_funct_1 @ X0))),
% 25.99/26.16      inference('sup+', [status(thm)], ['93', '94'])).
% 25.99/26.16  thf('96', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         (~ (v1_relat_1 @ X0)
% 25.99/26.16          | ~ (v1_funct_1 @ X0)
% 25.99/26.16          | (r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 25.99/26.16      inference('simplify', [status(thm)], ['95'])).
% 25.99/26.16  thf('97', plain,
% 25.99/26.16      (![X35 : $i]:
% 25.99/26.16         (((X35) = (k1_xboole_0)) | ~ (r1_tarski @ X35 @ k1_xboole_0))),
% 25.99/26.16      inference('cnf', [status(esa)], [t3_xboole_1])).
% 25.99/26.16  thf('98', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         (~ (v1_funct_1 @ X0)
% 25.99/26.16          | ~ (v1_relat_1 @ X0)
% 25.99/26.16          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 25.99/26.16      inference('sup-', [status(thm)], ['96', '97'])).
% 25.99/26.16  thf('99', plain,
% 25.99/26.16      (![X0 : $i]:
% 25.99/26.16         ((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.16           (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))
% 25.99/26.16           = (k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 25.99/26.16              (k9_relat_1 @ sk_C_1 @ X0)))),
% 25.99/26.16      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 25.99/26.16  thf('100', plain,
% 25.99/26.16      ((((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.17          (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))
% 25.99/26.17          = (k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ k1_xboole_0))
% 25.99/26.17        | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.17        | ~ (v1_funct_1 @ sk_C_1))),
% 25.99/26.17      inference('sup+', [status(thm)], ['98', '99'])).
% 25.99/26.17  thf('101', plain,
% 25.99/26.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['77', '78'])).
% 25.99/26.17  thf('102', plain,
% 25.99/26.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['77', '78'])).
% 25.99/26.17  thf('103', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('104', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('105', plain, (((k9_relat_1 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 25.99/26.17  thf('106', plain,
% 25.99/26.17      (((k1_xboole_0)
% 25.99/26.17         = (k9_relat_1 @ sk_C_1 @ 
% 25.99/26.17            (k3_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B))))),
% 25.99/26.17      inference('demod', [status(thm)], ['64', '105'])).
% 25.99/26.17  thf('107', plain,
% 25.99/26.17      (![X39 : $i, X40 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X39 @ (k6_subset_1 @ X39 @ X40))
% 25.99/26.17           = (k3_xboole_0 @ X39 @ X40))),
% 25.99/26.17      inference('demod', [status(thm)], ['1', '2', '3'])).
% 25.99/26.17  thf(commutativity_k2_xboole_0, axiom,
% 25.99/26.17    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 25.99/26.17  thf('108', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.99/26.17      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.99/26.17  thf(t7_xboole_1, axiom,
% 25.99/26.17    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 25.99/26.17  thf('109', plain,
% 25.99/26.17      (![X42 : $i, X43 : $i]: (r1_tarski @ X42 @ (k2_xboole_0 @ X42 @ X43))),
% 25.99/26.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 25.99/26.17  thf('110', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf(t12_xboole_1, axiom,
% 25.99/26.17    (![A:$i,B:$i]:
% 25.99/26.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 25.99/26.17  thf('111', plain,
% 25.99/26.17      (![X28 : $i, X29 : $i]:
% 25.99/26.17         (((k2_xboole_0 @ X29 @ X28) = (X28)) | ~ (r1_tarski @ X29 @ X28))),
% 25.99/26.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 25.99/26.17  thf('112', plain,
% 25.99/26.17      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))),
% 25.99/26.17      inference('sup-', [status(thm)], ['110', '111'])).
% 25.99/26.17  thf(t11_xboole_1, axiom,
% 25.99/26.17    (![A:$i,B:$i,C:$i]:
% 25.99/26.17     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 25.99/26.17  thf('113', plain,
% 25.99/26.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 25.99/26.17         ((r1_tarski @ X25 @ X26)
% 25.99/26.17          | ~ (r1_tarski @ (k2_xboole_0 @ X25 @ X27) @ X26))),
% 25.99/26.17      inference('cnf', [status(esa)], [t11_xboole_1])).
% 25.99/26.17  thf('114', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0) | (r1_tarski @ sk_A @ X0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['112', '113'])).
% 25.99/26.17  thf('115', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['109', '114'])).
% 25.99/26.17  thf('116', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 25.99/26.17      inference('sup+', [status(thm)], ['108', '115'])).
% 25.99/26.17  thf(t43_xboole_1, axiom,
% 25.99/26.17    (![A:$i,B:$i,C:$i]:
% 25.99/26.17     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 25.99/26.17       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 25.99/26.17  thf('117', plain,
% 25.99/26.17      (![X36 : $i, X37 : $i, X38 : $i]:
% 25.99/26.17         ((r1_tarski @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 25.99/26.17          | ~ (r1_tarski @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 25.99/26.17      inference('cnf', [status(esa)], [t43_xboole_1])).
% 25.99/26.17  thf('118', plain,
% 25.99/26.17      (![X44 : $i, X45 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.17  thf('119', plain,
% 25.99/26.17      (![X36 : $i, X37 : $i, X38 : $i]:
% 25.99/26.17         ((r1_tarski @ (k6_subset_1 @ X36 @ X37) @ X38)
% 25.99/26.17          | ~ (r1_tarski @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 25.99/26.17      inference('demod', [status(thm)], ['117', '118'])).
% 25.99/26.17  thf('120', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C_1))),
% 25.99/26.17      inference('sup-', [status(thm)], ['116', '119'])).
% 25.99/26.17  thf('121', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_C_1))),
% 25.99/26.17      inference('sup+', [status(thm)], ['107', '120'])).
% 25.99/26.17  thf(t146_funct_1, axiom,
% 25.99/26.17    (![A:$i,B:$i]:
% 25.99/26.17     ( ( v1_relat_1 @ B ) =>
% 25.99/26.17       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 25.99/26.17         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 25.99/26.17  thf('122', plain,
% 25.99/26.17      (![X60 : $i, X61 : $i]:
% 25.99/26.17         (~ (r1_tarski @ X60 @ (k1_relat_1 @ X61))
% 25.99/26.17          | (r1_tarski @ X60 @ (k10_relat_1 @ X61 @ (k9_relat_1 @ X61 @ X60)))
% 25.99/26.17          | ~ (v1_relat_1 @ X61))),
% 25.99/26.17      inference('cnf', [status(esa)], [t146_funct_1])).
% 25.99/26.17  thf('123', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (~ (v1_relat_1 @ sk_C_1)
% 25.99/26.17          | (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ 
% 25.99/26.17             (k10_relat_1 @ sk_C_1 @ 
% 25.99/26.17              (k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0)))))),
% 25.99/26.17      inference('sup-', [status(thm)], ['121', '122'])).
% 25.99/26.17  thf('124', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('125', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ 
% 25.99/26.17          (k10_relat_1 @ sk_C_1 @ 
% 25.99/26.17           (k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0))))),
% 25.99/26.17      inference('demod', [status(thm)], ['123', '124'])).
% 25.99/26.17  thf('126', plain,
% 25.99/26.17      ((r1_tarski @ (k3_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) @ 
% 25.99/26.17        (k10_relat_1 @ sk_C_1 @ k1_xboole_0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['106', '125'])).
% 25.99/26.17  thf('127', plain,
% 25.99/26.17      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.99/26.17         (((X11) = (k6_subset_1 @ X7 @ X8))
% 25.99/26.17          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 25.99/26.17          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.99/26.17      inference('demod', [status(thm)], ['5', '6'])).
% 25.99/26.17  thf('128', plain,
% 25.99/26.17      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.99/26.17         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 25.99/26.17          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 25.99/26.17          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.99/26.17      inference('cnf', [status(esa)], [d5_xboole_0])).
% 25.99/26.17  thf('129', plain,
% 25.99/26.17      (![X44 : $i, X45 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.17  thf('130', plain,
% 25.99/26.17      (![X7 : $i, X8 : $i, X11 : $i]:
% 25.99/26.17         (((X11) = (k6_subset_1 @ X7 @ X8))
% 25.99/26.17          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 25.99/26.17          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 25.99/26.17      inference('demod', [status(thm)], ['128', '129'])).
% 25.99/26.17  thf('131', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 25.99/26.17          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 25.99/26.17          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 25.99/26.17          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 25.99/26.17      inference('sup-', [status(thm)], ['127', '130'])).
% 25.99/26.17  thf('132', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (((X1) = (k6_subset_1 @ X0 @ X0))
% 25.99/26.17          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 25.99/26.17      inference('simplify', [status(thm)], ['131'])).
% 25.99/26.17  thf('133', plain,
% 25.99/26.17      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['29', '32'])).
% 25.99/26.17  thf('134', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (((X1) = (k5_xboole_0 @ X0 @ X0))
% 25.99/26.17          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 25.99/26.17      inference('demod', [status(thm)], ['132', '133'])).
% 25.99/26.17  thf('135', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (~ (v1_funct_1 @ X0)
% 25.99/26.17          | ~ (v1_relat_1 @ X0)
% 25.99/26.17          | ~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 25.99/26.17      inference('simplify', [status(thm)], ['91'])).
% 25.99/26.17  thf('136', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X1 @ X1))
% 25.99/26.17          | ~ (v1_relat_1 @ X0)
% 25.99/26.17          | ~ (v1_funct_1 @ X0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['134', '135'])).
% 25.99/26.17  thf('137', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['38', '39'])).
% 25.99/26.17  thf('138', plain, (((k9_relat_1 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 25.99/26.17  thf('139', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         ((k9_relat_1 @ sk_C_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['137', '138'])).
% 25.99/26.17  thf('140', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 25.99/26.17            = (k1_xboole_0))
% 25.99/26.17          | ~ (v1_funct_1 @ X0)
% 25.99/26.17          | ~ (v1_relat_1 @ X0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['136', '139'])).
% 25.99/26.17  thf('141', plain,
% 25.99/26.17      (![X58 : $i, X59 : $i]:
% 25.99/26.17         ((r1_tarski @ (k9_relat_1 @ X58 @ (k10_relat_1 @ X58 @ X59)) @ X59)
% 25.99/26.17          | ~ (v1_funct_1 @ X58)
% 25.99/26.17          | ~ (v1_relat_1 @ X58))),
% 25.99/26.17      inference('cnf', [status(esa)], [t145_funct_1])).
% 25.99/26.17  thf('142', plain,
% 25.99/26.17      (![X17 : $i, X19 : $i]:
% 25.99/26.17         (((X17) = (X19))
% 25.99/26.17          | ~ (r1_tarski @ X19 @ X17)
% 25.99/26.17          | ~ (r1_tarski @ X17 @ X19))),
% 25.99/26.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.99/26.17  thf('143', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (~ (v1_relat_1 @ X1)
% 25.99/26.17          | ~ (v1_funct_1 @ X1)
% 25.99/26.17          | ~ (r1_tarski @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 25.99/26.17          | ((X0) = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 25.99/26.17      inference('sup-', [status(thm)], ['141', '142'])).
% 25.99/26.17  thf('144', plain,
% 25.99/26.17      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 25.99/26.17        | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.17        | ~ (v1_funct_1 @ sk_C_1)
% 25.99/26.17        | ((k1_xboole_0)
% 25.99/26.17            = (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0)))
% 25.99/26.17        | ~ (v1_funct_1 @ sk_C_1)
% 25.99/26.17        | ~ (v1_relat_1 @ sk_C_1))),
% 25.99/26.17      inference('sup-', [status(thm)], ['140', '143'])).
% 25.99/26.17  thf('145', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['34', '37'])).
% 25.99/26.17  thf('146', plain,
% 25.99/26.17      (![X32 : $i, X33 : $i]: (r1_tarski @ (k6_subset_1 @ X32 @ X33) @ X32)),
% 25.99/26.17      inference('demod', [status(thm)], ['71', '72'])).
% 25.99/26.17  thf('147', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 25.99/26.17      inference('sup+', [status(thm)], ['145', '146'])).
% 25.99/26.17  thf('148', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('149', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('150', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('151', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('152', plain,
% 25.99/26.17      (((k1_xboole_0)
% 25.99/26.17         = (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0)))),
% 25.99/26.17      inference('demod', [status(thm)],
% 25.99/26.17                ['144', '147', '148', '149', '150', '151'])).
% 25.99/26.17  thf('153', plain,
% 25.99/26.17      (![X52 : $i, X53 : $i, X54 : $i]:
% 25.99/26.17         (~ (v2_funct_1 @ X52)
% 25.99/26.17          | ((k9_relat_1 @ X52 @ (k3_xboole_0 @ X53 @ X54))
% 25.99/26.17              = (k3_xboole_0 @ (k9_relat_1 @ X52 @ X53) @ 
% 25.99/26.17                 (k9_relat_1 @ X52 @ X54)))
% 25.99/26.17          | ~ (v1_funct_1 @ X52)
% 25.99/26.17          | ~ (v1_relat_1 @ X52))),
% 25.99/26.17      inference('cnf', [status(esa)], [t121_funct_1])).
% 25.99/26.17  thf('154', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.17            (k3_xboole_0 @ X0 @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0)))
% 25.99/26.17            = (k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ X0) @ k1_xboole_0))
% 25.99/26.17          | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.17          | ~ (v1_funct_1 @ sk_C_1)
% 25.99/26.17          | ~ (v2_funct_1 @ sk_C_1))),
% 25.99/26.17      inference('sup+', [status(thm)], ['152', '153'])).
% 25.99/26.17  thf('155', plain,
% 25.99/26.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['77', '78'])).
% 25.99/26.17  thf('156', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('157', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('158', plain, ((v2_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('159', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         ((k9_relat_1 @ sk_C_1 @ 
% 25.99/26.17           (k3_xboole_0 @ X0 @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0)))
% 25.99/26.17           = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['154', '155', '156', '157', '158'])).
% 25.99/26.17  thf('160', plain,
% 25.99/26.17      (![X0 : $i]:
% 25.99/26.17         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ 
% 25.99/26.17          (k10_relat_1 @ sk_C_1 @ 
% 25.99/26.17           (k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0))))),
% 25.99/26.17      inference('demod', [status(thm)], ['123', '124'])).
% 25.99/26.17  thf('161', plain,
% 25.99/26.17      ((r1_tarski @ 
% 25.99/26.17        (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0)) @ 
% 25.99/26.17        (k10_relat_1 @ sk_C_1 @ k1_xboole_0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['159', '160'])).
% 25.99/26.17  thf(d3_tarski, axiom,
% 25.99/26.17    (![A:$i,B:$i]:
% 25.99/26.17     ( ( r1_tarski @ A @ B ) <=>
% 25.99/26.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 25.99/26.17  thf('162', plain,
% 25.99/26.17      (![X3 : $i, X5 : $i]:
% 25.99/26.17         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 25.99/26.17      inference('cnf', [status(esa)], [d3_tarski])).
% 25.99/26.17  thf('163', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (~ (v1_funct_1 @ X0)
% 25.99/26.17          | ~ (v1_relat_1 @ X0)
% 25.99/26.17          | ~ (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 25.99/26.17      inference('simplify', [status(thm)], ['91'])).
% 25.99/26.17  thf('164', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         ((r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1)
% 25.99/26.17          | ~ (v1_relat_1 @ X0)
% 25.99/26.17          | ~ (v1_funct_1 @ X0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['162', '163'])).
% 25.99/26.17  thf('165', plain,
% 25.99/26.17      (![X17 : $i, X19 : $i]:
% 25.99/26.17         (((X17) = (X19))
% 25.99/26.17          | ~ (r1_tarski @ X19 @ X17)
% 25.99/26.17          | ~ (r1_tarski @ X17 @ X19))),
% 25.99/26.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.99/26.17  thf('166', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (~ (v1_funct_1 @ X1)
% 25.99/26.17          | ~ (v1_relat_1 @ X1)
% 25.99/26.17          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ k1_xboole_0))
% 25.99/26.17          | ((X0) = (k10_relat_1 @ X1 @ k1_xboole_0)))),
% 25.99/26.17      inference('sup-', [status(thm)], ['164', '165'])).
% 25.99/26.17  thf('167', plain,
% 25.99/26.17      ((((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0))
% 25.99/26.17          = (k10_relat_1 @ sk_C_1 @ k1_xboole_0))
% 25.99/26.17        | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.17        | ~ (v1_funct_1 @ sk_C_1))),
% 25.99/26.17      inference('sup-', [status(thm)], ['161', '166'])).
% 25.99/26.17  thf('168', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('169', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('170', plain,
% 25.99/26.17      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0))
% 25.99/26.17         = (k10_relat_1 @ sk_C_1 @ k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['167', '168', '169'])).
% 25.99/26.17  thf('171', plain,
% 25.99/26.17      ((r1_tarski @ 
% 25.99/26.17        (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0)) @ 
% 25.99/26.17        (k10_relat_1 @ sk_C_1 @ k1_xboole_0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['159', '160'])).
% 25.99/26.17  thf('172', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X1 @ X1))
% 25.99/26.17          | ~ (v1_relat_1 @ X0)
% 25.99/26.17          | ~ (v1_funct_1 @ X0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['134', '135'])).
% 25.99/26.17  thf('173', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['34', '37'])).
% 25.99/26.17  thf('174', plain,
% 25.99/26.17      (![X35 : $i]:
% 25.99/26.17         (((X35) = (k1_xboole_0)) | ~ (r1_tarski @ X35 @ k1_xboole_0))),
% 25.99/26.17      inference('cnf', [status(esa)], [t3_xboole_1])).
% 25.99/26.17  thf('175', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (~ (r1_tarski @ X1 @ (k6_subset_1 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 25.99/26.17      inference('sup-', [status(thm)], ['173', '174'])).
% 25.99/26.17  thf('176', plain,
% 25.99/26.17      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['29', '32'])).
% 25.99/26.17  thf('177', plain,
% 25.99/26.17      (![X0 : $i, X1 : $i]:
% 25.99/26.17         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 25.99/26.17      inference('demod', [status(thm)], ['175', '176'])).
% 25.99/26.17  thf('178', plain,
% 25.99/26.17      (![X0 : $i, X2 : $i]:
% 25.99/26.17         (~ (r1_tarski @ X2 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 25.99/26.17          | ~ (v1_funct_1 @ X0)
% 25.99/26.17          | ~ (v1_relat_1 @ X0)
% 25.99/26.17          | ((X2) = (k1_xboole_0)))),
% 25.99/26.17      inference('sup-', [status(thm)], ['172', '177'])).
% 25.99/26.17  thf('179', plain,
% 25.99/26.17      ((((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0))
% 25.99/26.17          = (k1_xboole_0))
% 25.99/26.17        | ~ (v1_relat_1 @ sk_C_1)
% 25.99/26.17        | ~ (v1_funct_1 @ sk_C_1))),
% 25.99/26.17      inference('sup-', [status(thm)], ['171', '178'])).
% 25.99/26.17  thf('180', plain, ((v1_relat_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('181', plain, ((v1_funct_1 @ sk_C_1)),
% 25.99/26.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.99/26.17  thf('182', plain,
% 25.99/26.17      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C_1 @ k1_xboole_0))
% 25.99/26.17         = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['179', '180', '181'])).
% 25.99/26.17  thf('183', plain, (((k10_relat_1 @ sk_C_1 @ k1_xboole_0) = (k1_xboole_0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['170', '182'])).
% 25.99/26.17  thf('184', plain,
% 25.99/26.17      ((r1_tarski @ (k3_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) @ 
% 25.99/26.17        k1_xboole_0)),
% 25.99/26.17      inference('demod', [status(thm)], ['126', '183'])).
% 25.99/26.17  thf('185', plain,
% 25.99/26.17      (![X35 : $i]:
% 25.99/26.17         (((X35) = (k1_xboole_0)) | ~ (r1_tarski @ X35 @ k1_xboole_0))),
% 25.99/26.17      inference('cnf', [status(esa)], [t3_xboole_1])).
% 25.99/26.17  thf('186', plain,
% 25.99/26.17      (((k3_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 25.99/26.17      inference('sup-', [status(thm)], ['184', '185'])).
% 25.99/26.17  thf('187', plain,
% 25.99/26.17      (![X23 : $i, X24 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X23 @ X24)
% 25.99/26.17           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 25.99/26.17      inference('demod', [status(thm)], ['30', '31'])).
% 25.99/26.17  thf('188', plain,
% 25.99/26.17      (((k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B))
% 25.99/26.17         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['186', '187'])).
% 25.99/26.17  thf('189', plain,
% 25.99/26.17      (![X39 : $i, X40 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X39 @ (k6_subset_1 @ X39 @ X40))
% 25.99/26.17           = (k3_xboole_0 @ X39 @ X40))),
% 25.99/26.17      inference('demod', [status(thm)], ['1', '2', '3'])).
% 25.99/26.17  thf('190', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 25.99/26.17      inference('sup+', [status(thm)], ['81', '84'])).
% 25.99/26.17  thf('191', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 25.99/26.17      inference('demod', [status(thm)], ['188', '189', '190'])).
% 25.99/26.17  thf('192', plain,
% 25.99/26.17      (![X23 : $i, X24 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X23 @ X24)
% 25.99/26.17           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 25.99/26.17      inference('demod', [status(thm)], ['30', '31'])).
% 25.99/26.17  thf('193', plain,
% 25.99/26.17      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.99/26.17      inference('sup+', [status(thm)], ['191', '192'])).
% 25.99/26.17  thf('194', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['38', '39'])).
% 25.99/26.17  thf('195', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 25.99/26.17      inference('demod', [status(thm)], ['193', '194'])).
% 25.99/26.17  thf('196', plain,
% 25.99/26.17      (![X20 : $i, X21 : $i]:
% 25.99/26.17         ((r1_tarski @ X20 @ X21)
% 25.99/26.17          | ((k4_xboole_0 @ X20 @ X21) != (k1_xboole_0)))),
% 25.99/26.17      inference('cnf', [status(esa)], [l32_xboole_1])).
% 25.99/26.17  thf('197', plain,
% 25.99/26.17      (![X44 : $i, X45 : $i]:
% 25.99/26.17         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 25.99/26.17      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 25.99/26.17  thf('198', plain,
% 25.99/26.17      (![X20 : $i, X21 : $i]:
% 25.99/26.17         ((r1_tarski @ X20 @ X21)
% 25.99/26.17          | ((k6_subset_1 @ X20 @ X21) != (k1_xboole_0)))),
% 25.99/26.17      inference('demod', [status(thm)], ['196', '197'])).
% 25.99/26.17  thf('199', plain,
% 25.99/26.17      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 25.99/26.17      inference('sup-', [status(thm)], ['195', '198'])).
% 25.99/26.17  thf('200', plain, ((r1_tarski @ sk_A @ sk_B)),
% 25.99/26.17      inference('simplify', [status(thm)], ['199'])).
% 25.99/26.17  thf('201', plain, ($false), inference('demod', [status(thm)], ['0', '200'])).
% 25.99/26.17  
% 25.99/26.17  % SZS output end Refutation
% 25.99/26.17  
% 25.99/26.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
