%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u1t2kTfvDp

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 248 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  711 (1978 expanded)
%              Number of equality atoms :   65 ( 163 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k6_subset_1 @ X31 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ( k6_subset_1 @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('46',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ ( k6_subset_1 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('54',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('56',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X8 @ X9 ) @ X10 )
      = ( k6_subset_1 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('63',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k6_subset_1 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['55','56','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','64'])).

thf('66',plain,
    ( ( k6_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k6_subset_1 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['35','67'])).

thf('69',plain,(
    ( k6_subset_1 @ sk_B @ sk_C_1 )
 != ( k6_subset_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','34','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u1t2kTfvDp
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.34/2.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.34/2.59  % Solved by: fo/fo7.sh
% 2.34/2.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.34/2.59  % done 3488 iterations in 2.140s
% 2.34/2.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.34/2.59  % SZS output start Refutation
% 2.34/2.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.34/2.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.34/2.59  thf(sk_A_type, type, sk_A: $i).
% 2.34/2.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.34/2.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.34/2.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.34/2.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.34/2.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.34/2.59  thf(sk_B_type, type, sk_B: $i).
% 2.34/2.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.34/2.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.34/2.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.34/2.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.34/2.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.34/2.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.34/2.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.34/2.59  thf(t32_subset_1, conjecture,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59       ( ![C:$i]:
% 2.34/2.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.34/2.59             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.34/2.59  thf(zf_stmt_0, negated_conjecture,
% 2.34/2.59    (~( ![A:$i,B:$i]:
% 2.34/2.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59          ( ![C:$i]:
% 2.34/2.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59              ( ( k7_subset_1 @ A @ B @ C ) =
% 2.34/2.59                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 2.34/2.59    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 2.34/2.59  thf('0', plain,
% 2.34/2.59      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 2.34/2.59         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 2.34/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.59  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.59  thf(d2_subset_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( ( v1_xboole_0 @ A ) =>
% 2.34/2.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.34/2.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.34/2.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.34/2.59  thf('2', plain,
% 2.34/2.59      (![X21 : $i, X22 : $i]:
% 2.34/2.59         (~ (m1_subset_1 @ X21 @ X22)
% 2.34/2.59          | (r2_hidden @ X21 @ X22)
% 2.34/2.59          | (v1_xboole_0 @ X22))),
% 2.34/2.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.34/2.59  thf('3', plain,
% 2.34/2.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.34/2.59        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.59      inference('sup-', [status(thm)], ['1', '2'])).
% 2.34/2.59  thf(fc1_subset_1, axiom,
% 2.34/2.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.34/2.59  thf('4', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 2.34/2.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.34/2.59  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('clc', [status(thm)], ['3', '4'])).
% 2.34/2.59  thf(d1_zfmisc_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.34/2.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.34/2.59  thf('6', plain,
% 2.34/2.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.34/2.59         (~ (r2_hidden @ X19 @ X18)
% 2.34/2.59          | (r1_tarski @ X19 @ X17)
% 2.34/2.59          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 2.34/2.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.34/2.59  thf('7', plain,
% 2.34/2.59      (![X17 : $i, X19 : $i]:
% 2.34/2.59         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 2.34/2.59      inference('simplify', [status(thm)], ['6'])).
% 2.34/2.59  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.34/2.59      inference('sup-', [status(thm)], ['5', '7'])).
% 2.34/2.59  thf(t28_xboole_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.34/2.59  thf('9', plain,
% 2.34/2.59      (![X4 : $i, X5 : $i]:
% 2.34/2.59         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.34/2.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.34/2.59  thf('10', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.34/2.59      inference('sup-', [status(thm)], ['8', '9'])).
% 2.34/2.59  thf(commutativity_k3_xboole_0, axiom,
% 2.34/2.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.34/2.59  thf('11', plain,
% 2.34/2.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.34/2.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.34/2.59  thf(t100_xboole_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.34/2.59  thf('12', plain,
% 2.34/2.59      (![X2 : $i, X3 : $i]:
% 2.34/2.59         ((k4_xboole_0 @ X2 @ X3)
% 2.34/2.59           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 2.34/2.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.34/2.59  thf(redefinition_k6_subset_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.34/2.59  thf('13', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('14', plain,
% 2.34/2.59      (![X2 : $i, X3 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X2 @ X3)
% 2.34/2.59           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 2.34/2.59      inference('demod', [status(thm)], ['12', '13'])).
% 2.34/2.59  thf('15', plain,
% 2.34/2.59      (![X0 : $i, X1 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X0 @ X1)
% 2.34/2.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.34/2.59      inference('sup+', [status(thm)], ['11', '14'])).
% 2.34/2.59  thf('16', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.34/2.59      inference('sup+', [status(thm)], ['10', '15'])).
% 2.34/2.59  thf('17', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.59  thf(d5_subset_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.34/2.59  thf('18', plain,
% 2.34/2.59      (![X24 : $i, X25 : $i]:
% 2.34/2.59         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 2.34/2.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 2.34/2.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.34/2.59  thf('19', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('20', plain,
% 2.34/2.59      (![X24 : $i, X25 : $i]:
% 2.34/2.59         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 2.34/2.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 2.34/2.59      inference('demod', [status(thm)], ['18', '19'])).
% 2.34/2.59  thf('21', plain,
% 2.34/2.59      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 2.34/2.59      inference('sup-', [status(thm)], ['17', '20'])).
% 2.34/2.59  thf('22', plain,
% 2.34/2.59      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.34/2.59      inference('sup+', [status(thm)], ['16', '21'])).
% 2.34/2.59  thf('23', plain,
% 2.34/2.59      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 2.34/2.59         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.34/2.59      inference('demod', [status(thm)], ['0', '22'])).
% 2.34/2.59  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.59  thf(redefinition_k7_subset_1, axiom,
% 2.34/2.59    (![A:$i,B:$i,C:$i]:
% 2.34/2.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.34/2.59  thf('25', plain,
% 2.34/2.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.34/2.59         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 2.34/2.59          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.34/2.59  thf('26', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('27', plain,
% 2.34/2.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.34/2.59         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 2.34/2.59          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k6_subset_1 @ X31 @ X33)))),
% 2.34/2.59      inference('demod', [status(thm)], ['25', '26'])).
% 2.34/2.59  thf('28', plain,
% 2.34/2.59      (![X0 : $i]:
% 2.34/2.59         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 2.34/2.59      inference('sup-', [status(thm)], ['24', '27'])).
% 2.34/2.59  thf('29', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_B @ sk_C_1)
% 2.34/2.59         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.34/2.59      inference('demod', [status(thm)], ['23', '28'])).
% 2.34/2.59  thf('30', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.34/2.59      inference('sup+', [status(thm)], ['10', '15'])).
% 2.34/2.59  thf(dt_k6_subset_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.34/2.59  thf('31', plain,
% 2.34/2.59      (![X26 : $i, X27 : $i]:
% 2.34/2.59         (m1_subset_1 @ (k6_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))),
% 2.34/2.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.34/2.59  thf('32', plain,
% 2.34/2.59      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('sup+', [status(thm)], ['30', '31'])).
% 2.34/2.59  thf(redefinition_k9_subset_1, axiom,
% 2.34/2.59    (![A:$i,B:$i,C:$i]:
% 2.34/2.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.59       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.34/2.59  thf('33', plain,
% 2.34/2.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.34/2.59         (((k9_subset_1 @ X36 @ X34 @ X35) = (k3_xboole_0 @ X34 @ X35))
% 2.34/2.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.34/2.59  thf('34', plain,
% 2.34/2.59      (![X0 : $i]:
% 2.34/2.59         ((k9_subset_1 @ sk_A @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 2.34/2.59           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.34/2.59      inference('sup-', [status(thm)], ['32', '33'])).
% 2.34/2.59  thf('35', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.34/2.59      inference('sup+', [status(thm)], ['10', '15'])).
% 2.34/2.59  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.59  thf('37', plain,
% 2.34/2.59      (![X21 : $i, X22 : $i]:
% 2.34/2.59         (~ (m1_subset_1 @ X21 @ X22)
% 2.34/2.59          | (r2_hidden @ X21 @ X22)
% 2.34/2.59          | (v1_xboole_0 @ X22))),
% 2.34/2.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.34/2.59  thf('38', plain,
% 2.34/2.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.34/2.59        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.59      inference('sup-', [status(thm)], ['36', '37'])).
% 2.34/2.59  thf('39', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 2.34/2.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.34/2.59  thf('40', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.59      inference('clc', [status(thm)], ['38', '39'])).
% 2.34/2.59  thf('41', plain,
% 2.34/2.59      (![X17 : $i, X19 : $i]:
% 2.34/2.59         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 2.34/2.59      inference('simplify', [status(thm)], ['6'])).
% 2.34/2.59  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.34/2.59      inference('sup-', [status(thm)], ['40', '41'])).
% 2.34/2.59  thf('43', plain,
% 2.34/2.59      (![X4 : $i, X5 : $i]:
% 2.34/2.59         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.34/2.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.34/2.59  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.34/2.59      inference('sup-', [status(thm)], ['42', '43'])).
% 2.34/2.59  thf('45', plain,
% 2.34/2.59      (![X0 : $i, X1 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X0 @ X1)
% 2.34/2.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.34/2.59      inference('sup+', [status(thm)], ['11', '14'])).
% 2.34/2.59  thf('46', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.34/2.59      inference('sup+', [status(thm)], ['44', '45'])).
% 2.34/2.59  thf(t48_xboole_1, axiom,
% 2.34/2.59    (![A:$i,B:$i]:
% 2.34/2.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.34/2.59  thf('47', plain,
% 2.34/2.59      (![X11 : $i, X12 : $i]:
% 2.34/2.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 2.34/2.59           = (k3_xboole_0 @ X11 @ X12))),
% 2.34/2.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.34/2.59  thf('48', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('49', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('50', plain,
% 2.34/2.59      (![X11 : $i, X12 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X11 @ (k6_subset_1 @ X11 @ X12))
% 2.34/2.59           = (k3_xboole_0 @ X11 @ X12))),
% 2.34/2.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.34/2.59  thf('51', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 2.34/2.59         = (k3_xboole_0 @ sk_A @ sk_B))),
% 2.34/2.59      inference('sup+', [status(thm)], ['46', '50'])).
% 2.34/2.59  thf('52', plain,
% 2.34/2.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.34/2.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.34/2.59  thf('53', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.34/2.59      inference('sup-', [status(thm)], ['42', '43'])).
% 2.34/2.59  thf('54', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 2.34/2.59      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.34/2.59  thf(t53_xboole_1, axiom,
% 2.34/2.59    (![A:$i,B:$i,C:$i]:
% 2.34/2.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 2.34/2.59       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 2.34/2.59  thf('55', plain,
% 2.34/2.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.34/2.59         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 2.34/2.59           = (k3_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 2.34/2.59              (k4_xboole_0 @ X13 @ X15)))),
% 2.34/2.59      inference('cnf', [status(esa)], [t53_xboole_1])).
% 2.34/2.59  thf('56', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf(t41_xboole_1, axiom,
% 2.34/2.59    (![A:$i,B:$i,C:$i]:
% 2.34/2.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.34/2.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.34/2.59  thf('57', plain,
% 2.34/2.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.34/2.59         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 2.34/2.59           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 2.34/2.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.34/2.59  thf('58', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('59', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('60', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('61', plain,
% 2.34/2.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.34/2.59         ((k6_subset_1 @ (k6_subset_1 @ X8 @ X9) @ X10)
% 2.34/2.59           = (k6_subset_1 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 2.34/2.59      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 2.34/2.59  thf('62', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('63', plain,
% 2.34/2.59      (![X29 : $i, X30 : $i]:
% 2.34/2.59         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 2.34/2.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.34/2.59  thf('64', plain,
% 2.34/2.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.34/2.59         ((k6_subset_1 @ (k6_subset_1 @ X13 @ X14) @ X15)
% 2.34/2.59           = (k3_xboole_0 @ (k6_subset_1 @ X13 @ X14) @ 
% 2.34/2.59              (k6_subset_1 @ X13 @ X15)))),
% 2.34/2.59      inference('demod', [status(thm)], ['55', '56', '61', '62', '63'])).
% 2.34/2.59  thf('65', plain,
% 2.34/2.59      (![X0 : $i]:
% 2.34/2.59         ((k6_subset_1 @ (k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 2.34/2.59           X0) = (k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ X0)))),
% 2.34/2.59      inference('sup+', [status(thm)], ['54', '64'])).
% 2.34/2.59  thf('66', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 2.34/2.59      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.34/2.59  thf('67', plain,
% 2.34/2.59      (![X0 : $i]:
% 2.34/2.59         ((k6_subset_1 @ sk_B @ X0)
% 2.34/2.59           = (k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ X0)))),
% 2.34/2.59      inference('demod', [status(thm)], ['65', '66'])).
% 2.34/2.59  thf('68', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_B @ sk_C_1)
% 2.34/2.59         = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.34/2.59      inference('sup+', [status(thm)], ['35', '67'])).
% 2.34/2.59  thf('69', plain,
% 2.34/2.59      (((k6_subset_1 @ sk_B @ sk_C_1) != (k6_subset_1 @ sk_B @ sk_C_1))),
% 2.34/2.59      inference('demod', [status(thm)], ['29', '34', '68'])).
% 2.34/2.59  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 2.34/2.59  
% 2.34/2.59  % SZS output end Refutation
% 2.34/2.59  
% 2.34/2.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
