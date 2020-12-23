%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e11NHS7UmP

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 138 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  628 (1038 expanded)
%              Number of equality atoms :   56 (  91 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( ( k2_subset_1 @ X28 )
      = ( k3_subset_1 @ X28 @ ( k1_subset_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X28: $i] :
      ( X28
      = ( k3_subset_1 @ X28 @ ( k1_subset_1 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X30 @ X29 ) @ ( k3_subset_1 @ X30 @ X31 ) )
      | ( r1_tarski @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('28',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k6_subset_1 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['25','38'])).

thf('40',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('46',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e11NHS7UmP
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.57/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.83  % Solved by: fo/fo7.sh
% 0.57/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.83  % done 1278 iterations in 0.412s
% 0.57/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.83  % SZS output start Refutation
% 0.57/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.83  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.57/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.57/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.83  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.57/0.83  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.57/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.83  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.57/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.83  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.57/0.83  thf(t32_subset_1, conjecture,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83       ( ![C:$i]:
% 0.57/0.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.57/0.83             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.57/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.83    (~( ![A:$i,B:$i]:
% 0.57/0.83        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83          ( ![C:$i]:
% 0.57/0.83            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.57/0.83                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.57/0.83    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.57/0.83  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf(t4_subset_1, axiom,
% 0.57/0.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.57/0.83  thf('1', plain,
% 0.57/0.83      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 0.57/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.57/0.83  thf(involutiveness_k3_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.57/0.83  thf('2', plain,
% 0.57/0.83      (![X18 : $i, X19 : $i]:
% 0.57/0.83         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.57/0.83          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.57/0.83      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.57/0.83  thf('3', plain,
% 0.57/0.83      (![X0 : $i]:
% 0.57/0.83         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.57/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.83  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.57/0.83  thf('4', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.57/0.83      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.57/0.83  thf(t22_subset_1, axiom,
% 0.57/0.83    (![A:$i]:
% 0.57/0.83     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.57/0.83  thf('5', plain,
% 0.57/0.83      (![X28 : $i]:
% 0.57/0.83         ((k2_subset_1 @ X28) = (k3_subset_1 @ X28 @ (k1_subset_1 @ X28)))),
% 0.57/0.83      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.57/0.83  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.57/0.83  thf('6', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.57/0.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.57/0.83  thf('7', plain,
% 0.57/0.83      (![X28 : $i]: ((X28) = (k3_subset_1 @ X28 @ (k1_subset_1 @ X28)))),
% 0.57/0.83      inference('demod', [status(thm)], ['5', '6'])).
% 0.57/0.83  thf('8', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.57/0.83      inference('sup+', [status(thm)], ['4', '7'])).
% 0.57/0.83  thf('9', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.57/0.83      inference('demod', [status(thm)], ['3', '8'])).
% 0.57/0.83  thf(t31_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83       ( ![C:$i]:
% 0.57/0.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83           ( ( r1_tarski @ B @ C ) <=>
% 0.57/0.83             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.57/0.83  thf('10', plain,
% 0.57/0.83      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.57/0.83         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.57/0.83          | ~ (r1_tarski @ (k3_subset_1 @ X30 @ X29) @ 
% 0.57/0.83               (k3_subset_1 @ X30 @ X31))
% 0.57/0.83          | (r1_tarski @ X31 @ X29)
% 0.57/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 0.57/0.83      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.57/0.83  thf('11', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]:
% 0.57/0.83         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.57/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.57/0.83          | (r1_tarski @ X0 @ X1)
% 0.57/0.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 0.57/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.57/0.83  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.57/0.83  thf('12', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.57/0.83      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.57/0.83  thf(dt_k2_subset_1, axiom,
% 0.57/0.83    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.57/0.83  thf('13', plain,
% 0.57/0.83      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.57/0.83      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.57/0.83  thf('14', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.57/0.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.57/0.83  thf('15', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.57/0.83      inference('demod', [status(thm)], ['13', '14'])).
% 0.57/0.83  thf('16', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]:
% 0.57/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 0.57/0.83      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.57/0.83  thf('17', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.57/0.83      inference('sup-', [status(thm)], ['0', '16'])).
% 0.57/0.83  thf(t28_xboole_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.83  thf('18', plain,
% 0.57/0.83      (![X8 : $i, X9 : $i]:
% 0.57/0.83         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.57/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.83  thf('19', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.57/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.57/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.83  thf('20', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.83  thf(t100_xboole_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.83  thf('21', plain,
% 0.57/0.83      (![X3 : $i, X4 : $i]:
% 0.57/0.83         ((k4_xboole_0 @ X3 @ X4)
% 0.57/0.83           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.57/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.83  thf(redefinition_k6_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.57/0.83  thf('22', plain,
% 0.57/0.83      (![X20 : $i, X21 : $i]:
% 0.57/0.83         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.57/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.57/0.83  thf('23', plain,
% 0.57/0.83      (![X3 : $i, X4 : $i]:
% 0.57/0.83         ((k6_subset_1 @ X3 @ X4)
% 0.57/0.83           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.57/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.57/0.83  thf('24', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]:
% 0.57/0.83         ((k6_subset_1 @ X0 @ X1)
% 0.57/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.83      inference('sup+', [status(thm)], ['20', '23'])).
% 0.57/0.83  thf('25', plain,
% 0.57/0.83      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.57/0.83      inference('sup+', [status(thm)], ['19', '24'])).
% 0.57/0.83  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf('27', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]:
% 0.57/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 0.57/0.83      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.57/0.83  thf('28', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.57/0.83      inference('sup-', [status(thm)], ['26', '27'])).
% 0.57/0.83  thf('29', plain,
% 0.57/0.83      (![X8 : $i, X9 : $i]:
% 0.57/0.83         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.57/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.83  thf('30', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.57/0.83      inference('sup-', [status(thm)], ['28', '29'])).
% 0.57/0.83  thf('31', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.83  thf(t112_xboole_1, axiom,
% 0.57/0.83    (![A:$i,B:$i,C:$i]:
% 0.57/0.83     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.57/0.83       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.57/0.83  thf('32', plain,
% 0.57/0.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.57/0.83         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 0.57/0.83           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 0.57/0.83      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.57/0.83  thf('33', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.83         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.57/0.83           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.57/0.83      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.83  thf('34', plain,
% 0.57/0.83      (![X0 : $i]:
% 0.57/0.83         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.57/0.83           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.57/0.83      inference('sup+', [status(thm)], ['30', '33'])).
% 0.57/0.83  thf('35', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.83  thf('36', plain,
% 0.57/0.83      (![X0 : $i]:
% 0.57/0.83         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.57/0.83           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.57/0.83      inference('demod', [status(thm)], ['34', '35'])).
% 0.57/0.83  thf('37', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i]:
% 0.57/0.83         ((k6_subset_1 @ X0 @ X1)
% 0.57/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.83      inference('sup+', [status(thm)], ['20', '23'])).
% 0.57/0.83  thf('38', plain,
% 0.57/0.83      (![X0 : $i]:
% 0.57/0.83         ((k6_subset_1 @ sk_B @ X0)
% 0.57/0.83           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.57/0.83      inference('demod', [status(thm)], ['36', '37'])).
% 0.57/0.83  thf('39', plain,
% 0.57/0.83      (((k6_subset_1 @ sk_B @ sk_C)
% 0.57/0.83         = (k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.57/0.83      inference('sup+', [status(thm)], ['25', '38'])).
% 0.57/0.83  thf('40', plain,
% 0.57/0.83      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.57/0.83         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf('41', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf(d5_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.57/0.83  thf('42', plain,
% 0.57/0.83      (![X13 : $i, X14 : $i]:
% 0.57/0.83         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.57/0.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.57/0.83      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.57/0.83  thf('43', plain,
% 0.57/0.83      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.57/0.83      inference('sup-', [status(thm)], ['41', '42'])).
% 0.57/0.83  thf('44', plain,
% 0.57/0.83      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.57/0.83         != (k9_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.57/0.83      inference('demod', [status(thm)], ['40', '43'])).
% 0.57/0.83  thf('45', plain,
% 0.57/0.83      (![X20 : $i, X21 : $i]:
% 0.57/0.83         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.57/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.57/0.83  thf('46', plain,
% 0.57/0.83      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.57/0.83         != (k9_subset_1 @ sk_A @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.57/0.83      inference('demod', [status(thm)], ['44', '45'])).
% 0.57/0.83  thf('47', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.83  thf(redefinition_k7_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i,C:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.57/0.83  thf('48', plain,
% 0.57/0.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.57/0.83         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.57/0.83          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.57/0.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.57/0.83  thf('49', plain,
% 0.57/0.83      (![X20 : $i, X21 : $i]:
% 0.57/0.83         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.57/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.57/0.83  thf('50', plain,
% 0.57/0.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.57/0.83         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.57/0.83          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 0.57/0.83      inference('demod', [status(thm)], ['48', '49'])).
% 0.57/0.83  thf('51', plain,
% 0.57/0.83      (![X0 : $i]:
% 0.57/0.83         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 0.57/0.83      inference('sup-', [status(thm)], ['47', '50'])).
% 0.57/0.83  thf('52', plain,
% 0.57/0.83      (((k6_subset_1 @ sk_B @ sk_C)
% 0.57/0.83         != (k9_subset_1 @ sk_A @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.57/0.83      inference('demod', [status(thm)], ['46', '51'])).
% 0.57/0.83  thf(dt_k6_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i]:
% 0.57/0.83     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.57/0.83  thf('53', plain,
% 0.57/0.83      (![X16 : $i, X17 : $i]:
% 0.57/0.83         (m1_subset_1 @ (k6_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))),
% 0.57/0.83      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.57/0.83  thf(redefinition_k9_subset_1, axiom,
% 0.57/0.83    (![A:$i,B:$i,C:$i]:
% 0.57/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.83       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.57/0.83  thf('54', plain,
% 0.57/0.83      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.57/0.83         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.57/0.83          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.57/0.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.57/0.83  thf('55', plain,
% 0.57/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.83         ((k9_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 0.57/0.83           = (k3_xboole_0 @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.57/0.83      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.83  thf('56', plain,
% 0.57/0.83      (((k6_subset_1 @ sk_B @ sk_C)
% 0.57/0.83         != (k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.57/0.83      inference('demod', [status(thm)], ['52', '55'])).
% 0.57/0.83  thf('57', plain, ($false),
% 0.57/0.83      inference('simplify_reflect-', [status(thm)], ['39', '56'])).
% 0.57/0.83  
% 0.57/0.83  % SZS output end Refutation
% 0.57/0.83  
% 0.57/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
