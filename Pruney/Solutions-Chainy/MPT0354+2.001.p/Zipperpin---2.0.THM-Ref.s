%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KG87MqewmB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 223 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  892 (2148 expanded)
%              Number of equality atoms :   66 ( 132 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t33_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
              = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k4_subset_1 @ X31 @ X30 @ X32 )
        = ( k2_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ sk_A @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X29 @ ( k3_subset_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','35'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X29 @ ( k3_subset_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['47','57'])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('75',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('78',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_subset_1 @ X20 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_C_1 @ X0 )
        = ( k4_subset_1 @ sk_A @ X0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_subset_1 @ sk_A @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k4_subset_1 @ sk_A @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KG87MqewmB
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 1069 iterations in 0.435s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.88  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(t33_subset_1, conjecture,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ![C:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 0.68/0.88             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i]:
% 0.68/0.88        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88          ( ![C:$i]:
% 0.68/0.88            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88              ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 0.68/0.88                ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t33_subset_1])).
% 0.68/0.88  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(d5_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (![X25 : $i, X26 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.68/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf(t36_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.68/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.88  thf(d1_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.88         (~ (r1_tarski @ X12 @ X13)
% 0.68/0.88          | (r2_hidden @ X12 @ X14)
% 0.68/0.88          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.68/0.88      inference('simplify', [status(thm)], ['4'])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '5'])).
% 0.68/0.88  thf(d2_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( v1_xboole_0 @ A ) =>
% 0.68/0.88         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.68/0.88       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.88         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X22 : $i, X23 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X22 @ X23)
% 0.68/0.88          | (m1_subset_1 @ X22 @ X23)
% 0.68/0.88          | (v1_xboole_0 @ X23))),
% 0.68/0.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.68/0.88          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.88  thf(fc1_subset_1, axiom,
% 0.68/0.88    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.88  thf('9', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('clc', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['2', '10'])).
% 0.68/0.88  thf('12', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k4_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.68/0.88       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.68/0.88          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 0.68/0.88          | ((k4_subset_1 @ X31 @ X30 @ X32) = (k2_xboole_0 @ X30 @ X32)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k4_subset_1 @ sk_A @ sk_C_1 @ X0) = (k2_xboole_0 @ sk_C_1 @ X0))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (((k4_subset_1 @ sk_A @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['11', '14'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k7_subset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.68/0.88         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k7_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.68/0.88          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k4_xboole_0 @ X33 @ X35)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.68/0.88         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['16', '19'])).
% 0.68/0.88  thf('21', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(involutiveness_k3_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (![X28 : $i, X29 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X29 @ (k3_subset_1 @ X29 @ X28)) = (X28))
% 0.68/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.68/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf('24', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X25 : $i, X26 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.68/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('clc', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X25 : $i, X26 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.68/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['26', '29'])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf(t48_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88           = (k3_xboole_0 @ X5 @ X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.68/0.88         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.68/0.88         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.68/0.88  thf('36', plain, (((sk_C_1) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['23', '35'])).
% 0.68/0.88  thf(t52_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.68/0.88       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf(commutativity_k2_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.68/0.88  thf(l51_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['41', '42'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.68/0.88           = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X5 : $i, X6 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.68/0.88           = (k3_xboole_0 @ X5 @ X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup+', [status(thm)], ['45', '46'])).
% 0.68/0.88  thf('48', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X28 : $i, X29 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X29 @ (k3_subset_1 @ X29 @ X28)) = (X28))
% 0.68/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.68/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['51', '52'])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup+', [status(thm)], ['45', '46'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.68/0.88  thf('57', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup+', [status(thm)], ['50', '56'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['47', '57'])).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.68/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.68/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.88  thf(t1_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.68/0.88       ( r1_tarski @ A @ C ) ))).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.88          | ~ (r1_tarski @ X1 @ X2)
% 0.68/0.88          | (r1_tarski @ X0 @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.88      inference('sup-', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['59', '62'])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.68/0.88      inference('simplify', [status(thm)], ['4'])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (r2_hidden @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 0.68/0.88          (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['63', '64'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (![X22 : $i, X23 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X22 @ X23)
% 0.68/0.88          | (m1_subset_1 @ X22 @ X23)
% 0.68/0.88          | (v1_xboole_0 @ X23))),
% 0.68/0.88      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.68/0.88  thf('67', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.68/0.88          | (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 0.68/0.88             (k1_zfmisc_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['65', '66'])).
% 0.68/0.88  thf('68', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 0.68/0.88          (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('clc', [status(thm)], ['67', '68'])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['58', '69'])).
% 0.68/0.88  thf('71', plain,
% 0.68/0.88      (![X25 : $i, X26 : $i]:
% 0.68/0.88         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.68/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.68/0.88           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.68/0.88         = (k2_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['44', '72'])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.68/0.88         = (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('demod', [status(thm)], ['73', '74'])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['20', '75'])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['2', '10'])).
% 0.68/0.88  thf('78', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(commutativity_k4_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.68/0.88       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.68/0.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.68/0.88          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k4_subset_1 @ X20 @ X21 @ X19)))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k4_subset_1 @ sk_A @ sk_C_1 @ X0)
% 0.68/0.88            = (k4_subset_1 @ sk_A @ X0 @ sk_C_1))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['78', '79'])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (((k4_subset_1 @ sk_A @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         = (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['77', '80'])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.68/0.88         != (k4_subset_1 @ sk_A @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('demod', [status(thm)], ['76', '81'])).
% 0.68/0.88  thf('83', plain, ($false),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['15', '82'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
