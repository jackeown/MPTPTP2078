%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzcUqKmR8d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:52 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 177 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  666 (1600 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X1 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      = ( k6_subset_1 @ sk_A @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('36',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k6_subset_1 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_B ) @ ( k10_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ( X0
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('56',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['34','56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzcUqKmR8d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1732 iterations in 0.773s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.25  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.06/1.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.25  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.06/1.25  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.06/1.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.25  thf(t158_funct_1, conjecture,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.06/1.25       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 1.06/1.25           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 1.06/1.25         ( r1_tarski @ A @ B ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i,B:$i,C:$i]:
% 1.06/1.25        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.06/1.25          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 1.06/1.25              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 1.06/1.25            ( r1_tarski @ A @ B ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 1.06/1.25  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(d10_xboole_0, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.25  thf('1', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.06/1.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.25  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.06/1.25      inference('simplify', [status(thm)], ['1'])).
% 1.06/1.25  thf(t12_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.06/1.25      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.25  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.25  thf(t7_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.25  thf('5', plain,
% 1.06/1.25      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.06/1.25      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.25  thf('6', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('7', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.06/1.25      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.25  thf('8', plain,
% 1.06/1.25      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.06/1.25      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf(t11_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.06/1.25         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 1.06/1.25      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | (r1_tarski @ sk_A @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['8', '9'])).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['5', '10'])).
% 1.06/1.25  thf(t43_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.06/1.25       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.06/1.25  thf('12', plain,
% 1.06/1.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.06/1.25         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.06/1.25          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.06/1.25  thf(redefinition_k6_subset_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.06/1.25  thf('13', plain,
% 1.06/1.25      (![X21 : $i, X22 : $i]:
% 1.06/1.25         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.25  thf('14', plain,
% 1.06/1.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.06/1.25         ((r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X13)
% 1.06/1.25          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('15', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 1.06/1.25      inference('sup-', [status(thm)], ['11', '14'])).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.06/1.25      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.06/1.25         ((r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X13)
% 1.06/1.25          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 1.06/1.25      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      (![X0 : $i, X2 : $i]:
% 1.06/1.25         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.25  thf('20', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X1 @ X1))
% 1.06/1.25          | ((X0) = (k6_subset_1 @ X1 @ X1)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['18', '19'])).
% 1.06/1.25  thf('21', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) = (k6_subset_1 @ X0 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['15', '20'])).
% 1.06/1.25  thf(t138_funct_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.06/1.25       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 1.06/1.25         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.06/1.25  thf('22', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.25         (((k10_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25))
% 1.06/1.25            = (k6_subset_1 @ (k10_relat_1 @ X23 @ X24) @ 
% 1.06/1.25               (k10_relat_1 @ X23 @ X25)))
% 1.06/1.25          | ~ (v1_funct_1 @ X23)
% 1.06/1.25          | ~ (v1_relat_1 @ X23))),
% 1.06/1.25      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0))
% 1.06/1.25            = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.06/1.25          | ~ (v1_relat_1 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ X1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['21', '22'])).
% 1.06/1.25  thf('24', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(t10_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.06/1.25  thf('25', plain,
% 1.06/1.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['24', '25'])).
% 1.06/1.25  thf('27', plain,
% 1.06/1.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.06/1.25         ((r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X13)
% 1.06/1.25          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('28', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 1.06/1.25      inference('sup-', [status(thm)], ['26', '27'])).
% 1.06/1.25  thf(t147_funct_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.25       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.06/1.25         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      (![X26 : $i, X27 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X26 @ (k2_relat_1 @ X27))
% 1.06/1.25          | ((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26)) = (X26))
% 1.06/1.25          | ~ (v1_funct_1 @ X27)
% 1.06/1.25          | ~ (v1_relat_1 @ X27))),
% 1.06/1.25      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ sk_C)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.25          | ((k9_relat_1 @ sk_C @ 
% 1.06/1.25              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 1.06/1.25              = (k6_subset_1 @ sk_A @ X0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['28', '29'])).
% 1.06/1.25  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('33', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 1.06/1.25           = (k6_subset_1 @ sk_A @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.06/1.25          = (k6_subset_1 @ sk_A @ sk_A))
% 1.06/1.25        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.25        | ~ (v1_relat_1 @ sk_C))),
% 1.06/1.25      inference('sup+', [status(thm)], ['23', '33'])).
% 1.06/1.25  thf('35', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.25         (((k10_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25))
% 1.06/1.25            = (k6_subset_1 @ (k10_relat_1 @ X23 @ X24) @ 
% 1.06/1.25               (k10_relat_1 @ X23 @ X25)))
% 1.06/1.25          | ~ (v1_funct_1 @ X23)
% 1.06/1.25          | ~ (v1_relat_1 @ X23))),
% 1.06/1.25      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.06/1.25  thf('36', plain,
% 1.06/1.25      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(t45_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( r1_tarski @ A @ B ) =>
% 1.06/1.25       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 1.06/1.25  thf('37', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i]:
% 1.06/1.25         (((X18) = (k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))
% 1.06/1.25          | ~ (r1_tarski @ X17 @ X18))),
% 1.06/1.25      inference('cnf', [status(esa)], [t45_xboole_1])).
% 1.06/1.25  thf('38', plain,
% 1.06/1.25      (![X21 : $i, X22 : $i]:
% 1.06/1.25         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.25  thf('39', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i]:
% 1.06/1.25         (((X18) = (k2_xboole_0 @ X17 @ (k6_subset_1 @ X18 @ X17)))
% 1.06/1.25          | ~ (r1_tarski @ X17 @ X18))),
% 1.06/1.25      inference('demod', [status(thm)], ['37', '38'])).
% 1.06/1.25  thf('40', plain,
% 1.06/1.25      (((k10_relat_1 @ sk_C @ sk_B)
% 1.06/1.25         = (k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 1.06/1.25            (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_B) @ 
% 1.06/1.25             (k10_relat_1 @ sk_C @ sk_A))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['36', '39'])).
% 1.06/1.25  thf('41', plain,
% 1.06/1.25      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.06/1.25      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.25  thf('42', plain,
% 1.06/1.25      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.06/1.25         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 1.06/1.25      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.06/1.25  thf('43', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.25  thf('44', plain,
% 1.06/1.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.06/1.25         ((r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X13)
% 1.06/1.25          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('45', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         (r1_tarski @ (k6_subset_1 @ X2 @ (k2_xboole_0 @ X2 @ X1)) @ X0)),
% 1.06/1.25      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.25  thf('46', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ 
% 1.06/1.25          (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 1.06/1.25           (k10_relat_1 @ sk_C @ sk_B)) @ 
% 1.06/1.25          X0)),
% 1.06/1.25      inference('sup+', [status(thm)], ['40', '45'])).
% 1.06/1.25  thf('47', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)
% 1.06/1.25          | ~ (v1_relat_1 @ sk_C)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_C))),
% 1.06/1.25      inference('sup+', [status(thm)], ['35', '46'])).
% 1.06/1.25  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('50', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)),
% 1.06/1.25      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.06/1.25  thf('51', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 1.06/1.25      inference('sup-', [status(thm)], ['11', '14'])).
% 1.06/1.25  thf('52', plain,
% 1.06/1.25      (![X0 : $i, X2 : $i]:
% 1.06/1.25         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.25  thf('53', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X0 @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.06/1.25          | ((X0) = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.25  thf('54', plain,
% 1.06/1.25      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 1.06/1.25         = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['50', '53'])).
% 1.06/1.25  thf('55', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 1.06/1.25           = (k6_subset_1 @ sk_A @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.06/1.25  thf('56', plain,
% 1.06/1.25      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.06/1.25         = (k6_subset_1 @ sk_A @ sk_B))),
% 1.06/1.25      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.25  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('59', plain,
% 1.06/1.25      (((k6_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['34', '56', '57', '58'])).
% 1.06/1.25  thf('60', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 1.06/1.25      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.25  thf('61', plain,
% 1.06/1.25      (![X0 : $i]: (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ X0)),
% 1.06/1.25      inference('sup+', [status(thm)], ['59', '60'])).
% 1.06/1.25  thf(t44_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.06/1.25       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.25  thf('62', plain,
% 1.06/1.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.25         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 1.06/1.25          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 1.06/1.25      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.06/1.25  thf('63', plain,
% 1.06/1.25      (![X21 : $i, X22 : $i]:
% 1.06/1.25         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.25  thf('64', plain,
% 1.06/1.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.25         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 1.06/1.25          | ~ (r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16))),
% 1.06/1.25      inference('demod', [status(thm)], ['62', '63'])).
% 1.06/1.25  thf('65', plain,
% 1.06/1.25      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['61', '64'])).
% 1.06/1.25  thf('66', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.06/1.25      inference('sup+', [status(thm)], ['4', '65'])).
% 1.06/1.25  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.08/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
