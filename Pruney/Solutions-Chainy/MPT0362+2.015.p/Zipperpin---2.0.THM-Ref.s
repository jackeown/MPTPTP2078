%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rfRGuoGDUu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:57 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 209 expanded)
%              Number of leaves         :   32 (  80 expanded)
%              Depth                    :   24
%              Number of atoms          :  780 (1494 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t42_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X20 ) @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('21',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ( r1_tarski @ ( k3_subset_1 @ X27 @ X26 ) @ ( k3_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = ( k3_subset_1 @ X25 @ ( k1_subset_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('29',plain,(
    ! [X25: $i] :
      ( X25
      = ( k3_subset_1 @ X25 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k3_subset_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X25: $i] :
      ( X25
      = ( k3_subset_1 @ X25 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X27 @ X26 ) @ ( k3_subset_1 @ X27 @ X28 ) )
      | ( r1_tarski @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('47',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( r1_tarski @ X29 @ ( k3_subset_1 @ X30 @ X31 ) )
      | ~ ( r1_tarski @ X31 @ ( k3_subset_1 @ X30 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','55'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X27 @ X26 ) @ ( k3_subset_1 @ X27 @ X28 ) )
      | ( r1_tarski @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['18','64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('67',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ( r1_tarski @ ( k3_subset_1 @ X27 @ X26 ) @ ( k3_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['4','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rfRGuoGDUu
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.80/2.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.80/2.03  % Solved by: fo/fo7.sh
% 1.80/2.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.03  % done 3223 iterations in 1.580s
% 1.80/2.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.80/2.03  % SZS output start Refutation
% 1.80/2.03  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.80/2.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.80/2.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/2.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.80/2.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/2.03  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.80/2.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.80/2.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/2.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.80/2.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.80/2.03  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/2.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.80/2.03  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.80/2.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.80/2.03  thf(t42_subset_1, conjecture,
% 1.80/2.03    (![A:$i,B:$i]:
% 1.80/2.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03       ( ![C:$i]:
% 1.80/2.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03           ( r1_tarski @
% 1.80/2.03             ( k3_subset_1 @ A @ B ) @ 
% 1.80/2.03             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.80/2.03  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.03    (~( ![A:$i,B:$i]:
% 1.80/2.03        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03          ( ![C:$i]:
% 1.80/2.03            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03              ( r1_tarski @
% 1.80/2.03                ( k3_subset_1 @ A @ B ) @ 
% 1.80/2.03                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 1.80/2.03    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 1.80/2.03  thf('0', plain,
% 1.80/2.03      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 1.80/2.03          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.80/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.03  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.80/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.03  thf(redefinition_k9_subset_1, axiom,
% 1.80/2.03    (![A:$i,B:$i,C:$i]:
% 1.80/2.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.80/2.03  thf('2', plain,
% 1.80/2.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.80/2.03         (((k9_subset_1 @ X24 @ X22 @ X23) = (k3_xboole_0 @ X22 @ X23))
% 1.80/2.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.80/2.03      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.80/2.03  thf('3', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 1.80/2.03      inference('sup-', [status(thm)], ['1', '2'])).
% 1.80/2.03  thf('4', plain,
% 1.80/2.03      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 1.80/2.03          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 1.80/2.03      inference('demod', [status(thm)], ['0', '3'])).
% 1.80/2.03  thf(dt_k2_subset_1, axiom,
% 1.80/2.03    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.80/2.03  thf('5', plain,
% 1.80/2.03      (![X20 : $i]: (m1_subset_1 @ (k2_subset_1 @ X20) @ (k1_zfmisc_1 @ X20))),
% 1.80/2.03      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.80/2.03  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.80/2.03  thf('6', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 1.80/2.03      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.80/2.03  thf('7', plain, (![X20 : $i]: (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X20))),
% 1.80/2.03      inference('demod', [status(thm)], ['5', '6'])).
% 1.80/2.03  thf(d2_subset_1, axiom,
% 1.80/2.03    (![A:$i,B:$i]:
% 1.80/2.03     ( ( ( v1_xboole_0 @ A ) =>
% 1.80/2.03         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.80/2.03       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.80/2.03         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.80/2.03  thf('8', plain,
% 1.80/2.03      (![X15 : $i, X16 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X15 @ X16)
% 1.80/2.03          | (r2_hidden @ X15 @ X16)
% 1.80/2.03          | (v1_xboole_0 @ X16))),
% 1.80/2.03      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.80/2.03  thf('9', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['7', '8'])).
% 1.80/2.03  thf(fc1_subset_1, axiom,
% 1.80/2.03    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.80/2.03  thf('10', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 1.80/2.03      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.80/2.03  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('clc', [status(thm)], ['9', '10'])).
% 1.80/2.03  thf(t17_xboole_1, axiom,
% 1.80/2.03    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.80/2.03  thf('12', plain,
% 1.80/2.03      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.80/2.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.80/2.03  thf(t79_zfmisc_1, axiom,
% 1.80/2.03    (![A:$i,B:$i]:
% 1.80/2.03     ( ( r1_tarski @ A @ B ) =>
% 1.80/2.03       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.80/2.03  thf('13', plain,
% 1.80/2.03      (![X13 : $i, X14 : $i]:
% 1.80/2.03         ((r1_tarski @ (k1_zfmisc_1 @ X13) @ (k1_zfmisc_1 @ X14))
% 1.80/2.03          | ~ (r1_tarski @ X13 @ X14))),
% 1.80/2.03      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.80/2.03  thf('14', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (r1_tarski @ (k1_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.80/2.03          (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['12', '13'])).
% 1.80/2.03  thf(d3_tarski, axiom,
% 1.80/2.03    (![A:$i,B:$i]:
% 1.80/2.03     ( ( r1_tarski @ A @ B ) <=>
% 1.80/2.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.80/2.03  thf('15', plain,
% 1.80/2.03      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.80/2.03         (~ (r2_hidden @ X3 @ X4)
% 1.80/2.03          | (r2_hidden @ X3 @ X5)
% 1.80/2.03          | ~ (r1_tarski @ X4 @ X5))),
% 1.80/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.03  thf('16', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.03         ((r2_hidden @ X2 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 1.80/2.03      inference('sup-', [status(thm)], ['14', '15'])).
% 1.80/2.03  thf('17', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (r2_hidden @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.80/2.03      inference('sup-', [status(thm)], ['11', '16'])).
% 1.80/2.03  thf('18', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.80/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.03  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('clc', [status(thm)], ['9', '10'])).
% 1.80/2.03  thf(t4_subset_1, axiom,
% 1.80/2.03    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.80/2.03  thf('20', plain,
% 1.80/2.03      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 1.80/2.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.80/2.03  thf('21', plain, (![X20 : $i]: (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X20))),
% 1.80/2.03      inference('demod', [status(thm)], ['5', '6'])).
% 1.80/2.03  thf(t31_subset_1, axiom,
% 1.80/2.03    (![A:$i,B:$i]:
% 1.80/2.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03       ( ![C:$i]:
% 1.80/2.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03           ( ( r1_tarski @ B @ C ) <=>
% 1.80/2.03             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.80/2.03  thf('22', plain,
% 1.80/2.03      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.80/2.03          | ~ (r1_tarski @ X28 @ X26)
% 1.80/2.03          | (r1_tarski @ (k3_subset_1 @ X27 @ X26) @ (k3_subset_1 @ X27 @ X28))
% 1.80/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.80/2.03      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.80/2.03  thf('23', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 1.80/2.03          | ~ (r1_tarski @ X1 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['21', '22'])).
% 1.80/2.03  thf('24', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.80/2.03          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ 
% 1.80/2.03             (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['20', '23'])).
% 1.80/2.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.80/2.03  thf('25', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 1.80/2.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.80/2.03  thf(t22_subset_1, axiom,
% 1.80/2.03    (![A:$i]:
% 1.80/2.03     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.80/2.03  thf('26', plain,
% 1.80/2.03      (![X25 : $i]:
% 1.80/2.03         ((k2_subset_1 @ X25) = (k3_subset_1 @ X25 @ (k1_subset_1 @ X25)))),
% 1.80/2.03      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.80/2.03  thf('27', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 1.80/2.03      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.80/2.03  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.80/2.03  thf('28', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 1.80/2.03      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.80/2.03  thf('29', plain, (![X25 : $i]: ((X25) = (k3_subset_1 @ X25 @ k1_xboole_0))),
% 1.80/2.03      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.80/2.03  thf('30', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 1.80/2.03      inference('demod', [status(thm)], ['24', '25', '29'])).
% 1.80/2.03  thf('31', plain,
% 1.80/2.03      (![X13 : $i, X14 : $i]:
% 1.80/2.03         ((r1_tarski @ (k1_zfmisc_1 @ X13) @ (k1_zfmisc_1 @ X14))
% 1.80/2.03          | ~ (r1_tarski @ X13 @ X14))),
% 1.80/2.03      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.80/2.03  thf('32', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (r1_tarski @ (k1_zfmisc_1 @ (k3_subset_1 @ X0 @ X0)) @ 
% 1.80/2.03          (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['30', '31'])).
% 1.80/2.03  thf('33', plain,
% 1.80/2.03      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.80/2.03         (~ (r2_hidden @ X3 @ X4)
% 1.80/2.03          | (r2_hidden @ X3 @ X5)
% 1.80/2.03          | ~ (r1_tarski @ X4 @ X5))),
% 1.80/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.03  thf('34', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k3_subset_1 @ X0 @ X0))))),
% 1.80/2.03      inference('sup-', [status(thm)], ['32', '33'])).
% 1.80/2.03  thf('35', plain,
% 1.80/2.03      (![X0 : $i]: (r2_hidden @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['19', '34'])).
% 1.80/2.03  thf('36', plain,
% 1.80/2.03      (![X15 : $i, X16 : $i]:
% 1.80/2.03         (~ (r2_hidden @ X15 @ X16)
% 1.80/2.03          | (m1_subset_1 @ X15 @ X16)
% 1.80/2.03          | (v1_xboole_0 @ X16))),
% 1.80/2.03      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.80/2.03  thf(d1_xboole_0, axiom,
% 1.80/2.03    (![A:$i]:
% 1.80/2.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.80/2.03  thf('37', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.80/2.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.80/2.03  thf('38', plain,
% 1.80/2.03      (![X15 : $i, X16 : $i]:
% 1.80/2.03         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 1.80/2.03      inference('clc', [status(thm)], ['36', '37'])).
% 1.80/2.03  thf('39', plain,
% 1.80/2.03      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['35', '38'])).
% 1.80/2.03  thf('40', plain, (![X25 : $i]: ((X25) = (k3_subset_1 @ X25 @ k1_xboole_0))),
% 1.80/2.03      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.80/2.03  thf('41', plain,
% 1.80/2.03      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.80/2.03          | ~ (r1_tarski @ (k3_subset_1 @ X27 @ X26) @ 
% 1.80/2.03               (k3_subset_1 @ X27 @ X28))
% 1.80/2.03          | (r1_tarski @ X28 @ X26)
% 1.80/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.80/2.03      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.80/2.03  thf('42', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 1.80/2.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | (r1_tarski @ X1 @ k1_xboole_0)
% 1.80/2.03          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['40', '41'])).
% 1.80/2.03  thf('43', plain,
% 1.80/2.03      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 1.80/2.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.80/2.03  thf('44', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 1.80/2.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | (r1_tarski @ X1 @ k1_xboole_0))),
% 1.80/2.03      inference('demod', [status(thm)], ['42', '43'])).
% 1.80/2.03  thf('45', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)
% 1.80/2.03          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0))))),
% 1.80/2.03      inference('sup-', [status(thm)], ['39', '44'])).
% 1.80/2.03  thf('46', plain,
% 1.80/2.03      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['35', '38'])).
% 1.80/2.03  thf('47', plain, (![X20 : $i]: (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X20))),
% 1.80/2.03      inference('demod', [status(thm)], ['5', '6'])).
% 1.80/2.03  thf(t35_subset_1, axiom,
% 1.80/2.03    (![A:$i,B:$i]:
% 1.80/2.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03       ( ![C:$i]:
% 1.80/2.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.03           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 1.80/2.03             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.80/2.03  thf('48', plain,
% 1.80/2.03      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.80/2.03          | (r1_tarski @ X29 @ (k3_subset_1 @ X30 @ X31))
% 1.80/2.03          | ~ (r1_tarski @ X31 @ (k3_subset_1 @ X30 @ X29))
% 1.80/2.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.80/2.03      inference('cnf', [status(esa)], [t35_subset_1])).
% 1.80/2.03  thf('49', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.80/2.03          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0))
% 1.80/2.03          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['47', '48'])).
% 1.80/2.03  thf('50', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         ((r1_tarski @ X0 @ (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)))
% 1.80/2.03          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X0)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['46', '49'])).
% 1.80/2.03  thf('51', plain,
% 1.80/2.03      (![X4 : $i, X6 : $i]:
% 1.80/2.03         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.80/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.03  thf('52', plain,
% 1.80/2.03      (![X4 : $i, X6 : $i]:
% 1.80/2.03         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.80/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.03  thf('53', plain,
% 1.80/2.03      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.80/2.03      inference('sup-', [status(thm)], ['51', '52'])).
% 1.80/2.03  thf('54', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.80/2.03      inference('simplify', [status(thm)], ['53'])).
% 1.80/2.03  thf('55', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 1.80/2.03      inference('demod', [status(thm)], ['50', '54'])).
% 1.80/2.03  thf('56', plain,
% 1.80/2.03      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)),
% 1.80/2.03      inference('demod', [status(thm)], ['45', '55'])).
% 1.80/2.03  thf(t1_xboole_1, axiom,
% 1.80/2.03    (![A:$i,B:$i,C:$i]:
% 1.80/2.03     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.80/2.03       ( r1_tarski @ A @ C ) ))).
% 1.80/2.03  thf('57', plain,
% 1.80/2.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.80/2.03         (~ (r1_tarski @ X9 @ X10)
% 1.80/2.03          | ~ (r1_tarski @ X10 @ X11)
% 1.80/2.03          | (r1_tarski @ X9 @ X11))),
% 1.80/2.03      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.80/2.03  thf('58', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1)
% 1.80/2.03          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 1.80/2.03      inference('sup-', [status(thm)], ['56', '57'])).
% 1.80/2.03  thf('59', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 1.80/2.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.80/2.03  thf('60', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1)),
% 1.80/2.03      inference('demod', [status(thm)], ['58', '59'])).
% 1.80/2.03  thf('61', plain,
% 1.80/2.03      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.80/2.03          | ~ (r1_tarski @ (k3_subset_1 @ X27 @ X26) @ 
% 1.80/2.03               (k3_subset_1 @ X27 @ X28))
% 1.80/2.03          | (r1_tarski @ X28 @ X26)
% 1.80/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.80/2.03      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.80/2.03  thf('62', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.80/2.03          | (r1_tarski @ X0 @ X1)
% 1.80/2.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['60', '61'])).
% 1.80/2.03  thf('63', plain, (![X20 : $i]: (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X20))),
% 1.80/2.03      inference('demod', [status(thm)], ['5', '6'])).
% 1.80/2.03  thf('64', plain,
% 1.80/2.03      (![X0 : $i, X1 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 1.80/2.03      inference('demod', [status(thm)], ['62', '63'])).
% 1.80/2.03  thf('65', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.80/2.03      inference('sup-', [status(thm)], ['18', '64'])).
% 1.80/2.03  thf('66', plain,
% 1.80/2.03      (![X13 : $i, X14 : $i]:
% 1.80/2.03         ((r1_tarski @ (k1_zfmisc_1 @ X13) @ (k1_zfmisc_1 @ X14))
% 1.80/2.03          | ~ (r1_tarski @ X13 @ X14))),
% 1.80/2.03      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.80/2.03  thf('67', plain,
% 1.80/2.03      ((r1_tarski @ (k1_zfmisc_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 1.80/2.03      inference('sup-', [status(thm)], ['65', '66'])).
% 1.80/2.03  thf('68', plain,
% 1.80/2.03      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.80/2.03         (~ (r2_hidden @ X3 @ X4)
% 1.80/2.03          | (r2_hidden @ X3 @ X5)
% 1.80/2.03          | ~ (r1_tarski @ X4 @ X5))),
% 1.80/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.03  thf('69', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.80/2.03          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B_1)))),
% 1.80/2.03      inference('sup-', [status(thm)], ['67', '68'])).
% 1.80/2.03  thf('70', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (r2_hidden @ (k3_xboole_0 @ sk_B_1 @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 1.80/2.03      inference('sup-', [status(thm)], ['17', '69'])).
% 1.80/2.03  thf('71', plain,
% 1.80/2.03      (![X15 : $i, X16 : $i]:
% 1.80/2.03         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 1.80/2.03      inference('clc', [status(thm)], ['36', '37'])).
% 1.80/2.03  thf('72', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (m1_subset_1 @ (k3_xboole_0 @ sk_B_1 @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 1.80/2.03      inference('sup-', [status(thm)], ['70', '71'])).
% 1.80/2.03  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.80/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.03  thf('74', plain,
% 1.80/2.03      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.80/2.03          | ~ (r1_tarski @ X28 @ X26)
% 1.80/2.03          | (r1_tarski @ (k3_subset_1 @ X27 @ X26) @ (k3_subset_1 @ X27 @ X28))
% 1.80/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.80/2.03      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.80/2.03  thf('75', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.80/2.03          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 1.80/2.03             (k3_subset_1 @ sk_A @ X0))
% 1.80/2.03          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 1.80/2.03      inference('sup-', [status(thm)], ['73', '74'])).
% 1.80/2.03  thf('76', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (~ (r1_tarski @ (k3_xboole_0 @ sk_B_1 @ X0) @ sk_B_1)
% 1.80/2.03          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 1.80/2.03             (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0))))),
% 1.80/2.03      inference('sup-', [status(thm)], ['72', '75'])).
% 1.80/2.03  thf('77', plain,
% 1.80/2.03      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.80/2.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.80/2.03  thf('78', plain,
% 1.80/2.03      (![X0 : $i]:
% 1.80/2.03         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ 
% 1.80/2.03          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 1.80/2.03      inference('demod', [status(thm)], ['76', '77'])).
% 1.80/2.03  thf('79', plain, ($false), inference('demod', [status(thm)], ['4', '78'])).
% 1.80/2.03  
% 1.80/2.03  % SZS output end Refutation
% 1.80/2.03  
% 1.80/2.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
