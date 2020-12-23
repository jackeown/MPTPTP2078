%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n3n0Kyox1W

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:50 EST 2020

% Result     : Theorem 5.54s
% Output     : Refutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 404 expanded)
%              Number of leaves         :   28 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          :  923 (3328 expanded)
%              Number of equality atoms :   66 ( 224 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k4_subset_1 @ X42 @ X41 @ X43 )
        = ( k2_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_tarski @ X29 @ X27 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('30',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['28','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('48',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('78',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['71','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('84',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( m1_subset_1 @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','89'])).

thf('91',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','92'])).

thf('94',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['71','76','77','78','79'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('96',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['8','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n3n0Kyox1W
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.54/5.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.54/5.76  % Solved by: fo/fo7.sh
% 5.54/5.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.54/5.76  % done 8157 iterations in 5.307s
% 5.54/5.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.54/5.76  % SZS output start Refutation
% 5.54/5.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.54/5.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.54/5.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.54/5.76  thf(sk_A_type, type, sk_A: $i).
% 5.54/5.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.54/5.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.54/5.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.54/5.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.54/5.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.54/5.76  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.54/5.76  thf(sk_B_type, type, sk_B: $i).
% 5.54/5.76  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.54/5.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.54/5.76  thf(t41_subset_1, conjecture,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.54/5.76       ( ![C:$i]:
% 5.54/5.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.54/5.76           ( r1_tarski @
% 5.54/5.76             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 5.54/5.76             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 5.54/5.76  thf(zf_stmt_0, negated_conjecture,
% 5.54/5.76    (~( ![A:$i,B:$i]:
% 5.54/5.76        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.54/5.76          ( ![C:$i]:
% 5.54/5.76            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.54/5.76              ( r1_tarski @
% 5.54/5.76                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 5.54/5.76                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 5.54/5.76    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 5.54/5.76  thf('0', plain,
% 5.54/5.76      (~ (r1_tarski @ 
% 5.54/5.76          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 5.54/5.76          (k3_subset_1 @ sk_A @ sk_B))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf(redefinition_k4_subset_1, axiom,
% 5.54/5.76    (![A:$i,B:$i,C:$i]:
% 5.54/5.76     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.54/5.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.54/5.76       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.54/5.76  thf('3', plain,
% 5.54/5.76      (![X41 : $i, X42 : $i, X43 : $i]:
% 5.54/5.76         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 5.54/5.76          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42))
% 5.54/5.76          | ((k4_subset_1 @ X42 @ X41 @ X43) = (k2_xboole_0 @ X41 @ X43)))),
% 5.54/5.76      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.54/5.76  thf('4', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 5.54/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 5.54/5.76      inference('sup-', [status(thm)], ['2', '3'])).
% 5.54/5.76  thf('5', plain,
% 5.54/5.76      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 5.54/5.76      inference('sup-', [status(thm)], ['1', '4'])).
% 5.54/5.76  thf(commutativity_k2_xboole_0, axiom,
% 5.54/5.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.54/5.76  thf('6', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.76  thf('7', plain,
% 5.54/5.76      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 5.54/5.76      inference('demod', [status(thm)], ['5', '6'])).
% 5.54/5.76  thf('8', plain,
% 5.54/5.76      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 5.54/5.76          (k3_subset_1 @ sk_A @ sk_B))),
% 5.54/5.76      inference('demod', [status(thm)], ['0', '7'])).
% 5.54/5.76  thf('9', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.76  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf(d5_subset_1, axiom,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.54/5.76       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.54/5.76  thf('11', plain,
% 5.54/5.76      (![X34 : $i, X35 : $i]:
% 5.54/5.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 5.54/5.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 5.54/5.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.54/5.76  thf('12', plain,
% 5.54/5.76      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 5.54/5.76      inference('sup-', [status(thm)], ['10', '11'])).
% 5.54/5.76  thf(t41_xboole_1, axiom,
% 5.54/5.76    (![A:$i,B:$i,C:$i]:
% 5.54/5.76     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 5.54/5.76       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.54/5.76  thf('13', plain,
% 5.54/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.54/5.76           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.54/5.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.54/5.76  thf('14', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 5.54/5.76           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 5.54/5.76      inference('sup+', [status(thm)], ['12', '13'])).
% 5.54/5.76  thf('15', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 5.54/5.76           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 5.54/5.76      inference('sup+', [status(thm)], ['9', '14'])).
% 5.54/5.76  thf('16', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf('17', plain,
% 5.54/5.76      (![X34 : $i, X35 : $i]:
% 5.54/5.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 5.54/5.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 5.54/5.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.54/5.76  thf('18', plain,
% 5.54/5.76      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 5.54/5.76      inference('sup-', [status(thm)], ['16', '17'])).
% 5.54/5.76  thf('19', plain,
% 5.54/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.54/5.76           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.54/5.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.54/5.76  thf('20', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 5.54/5.76           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 5.54/5.76      inference('sup+', [status(thm)], ['18', '19'])).
% 5.54/5.76  thf('21', plain,
% 5.54/5.76      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B)
% 5.54/5.76         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 5.54/5.76      inference('sup+', [status(thm)], ['15', '20'])).
% 5.54/5.76  thf(t36_xboole_1, axiom,
% 5.54/5.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.54/5.76  thf('22', plain,
% 5.54/5.76      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 5.54/5.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.54/5.76  thf('23', plain,
% 5.54/5.76      ((r1_tarski @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B) @ 
% 5.54/5.76        (k3_subset_1 @ sk_A @ sk_B))),
% 5.54/5.76      inference('sup+', [status(thm)], ['21', '22'])).
% 5.54/5.76  thf('24', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf(d2_subset_1, axiom,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( ( v1_xboole_0 @ A ) =>
% 5.54/5.76         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 5.54/5.76       ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.54/5.76         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 5.54/5.76  thf('25', plain,
% 5.54/5.76      (![X31 : $i, X32 : $i]:
% 5.54/5.76         (~ (m1_subset_1 @ X31 @ X32)
% 5.54/5.76          | (r2_hidden @ X31 @ X32)
% 5.54/5.76          | (v1_xboole_0 @ X32))),
% 5.54/5.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.54/5.76  thf('26', plain,
% 5.54/5.76      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 5.54/5.76        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 5.54/5.76      inference('sup-', [status(thm)], ['24', '25'])).
% 5.54/5.76  thf(fc1_subset_1, axiom,
% 5.54/5.76    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.54/5.76  thf('27', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 5.54/5.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 5.54/5.76  thf('28', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('clc', [status(thm)], ['26', '27'])).
% 5.54/5.76  thf(d1_zfmisc_1, axiom,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 5.54/5.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 5.54/5.76  thf('29', plain,
% 5.54/5.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.54/5.76         (~ (r2_hidden @ X29 @ X28)
% 5.54/5.76          | (r1_tarski @ X29 @ X27)
% 5.54/5.76          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 5.54/5.76      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.54/5.76  thf('30', plain,
% 5.54/5.76      (![X27 : $i, X29 : $i]:
% 5.54/5.76         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 5.54/5.76      inference('simplify', [status(thm)], ['29'])).
% 5.54/5.76  thf('31', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 5.54/5.76      inference('sup-', [status(thm)], ['28', '30'])).
% 5.54/5.76  thf(t12_xboole_1, axiom,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.54/5.76  thf('32', plain,
% 5.54/5.76      (![X8 : $i, X9 : $i]:
% 5.54/5.76         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 5.54/5.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.54/5.76  thf('33', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 5.54/5.76      inference('sup-', [status(thm)], ['31', '32'])).
% 5.54/5.76  thf('34', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.76  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.76  thf('36', plain,
% 5.54/5.76      (![X31 : $i, X32 : $i]:
% 5.54/5.76         (~ (m1_subset_1 @ X31 @ X32)
% 5.54/5.76          | (r2_hidden @ X31 @ X32)
% 5.54/5.76          | (v1_xboole_0 @ X32))),
% 5.54/5.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.54/5.76  thf('37', plain,
% 5.54/5.76      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 5.54/5.76        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 5.54/5.76      inference('sup-', [status(thm)], ['35', '36'])).
% 5.54/5.76  thf('38', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 5.54/5.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 5.54/5.76  thf('39', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 5.54/5.76      inference('clc', [status(thm)], ['37', '38'])).
% 5.54/5.76  thf('40', plain,
% 5.54/5.76      (![X27 : $i, X29 : $i]:
% 5.54/5.76         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 5.54/5.76      inference('simplify', [status(thm)], ['29'])).
% 5.54/5.76  thf('41', plain, ((r1_tarski @ sk_B @ sk_A)),
% 5.54/5.76      inference('sup-', [status(thm)], ['39', '40'])).
% 5.54/5.76  thf('42', plain,
% 5.54/5.76      (![X8 : $i, X9 : $i]:
% 5.54/5.76         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 5.54/5.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.54/5.76  thf('43', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 5.54/5.76      inference('sup-', [status(thm)], ['41', '42'])).
% 5.54/5.76  thf(t46_xboole_1, axiom,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 5.54/5.76  thf('44', plain,
% 5.54/5.76      (![X19 : $i, X20 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 5.54/5.76      inference('cnf', [status(esa)], [t46_xboole_1])).
% 5.54/5.76  thf('45', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 5.54/5.76      inference('sup+', [status(thm)], ['43', '44'])).
% 5.54/5.76  thf(t44_xboole_1, axiom,
% 5.54/5.76    (![A:$i,B:$i,C:$i]:
% 5.54/5.76     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 5.54/5.76       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.54/5.76  thf('46', plain,
% 5.54/5.76      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.54/5.76         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 5.54/5.76          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 5.54/5.76      inference('cnf', [status(esa)], [t44_xboole_1])).
% 5.54/5.76  thf('47', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 5.54/5.76          | (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.54/5.76      inference('sup-', [status(thm)], ['45', '46'])).
% 5.54/5.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.54/5.76  thf('48', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 5.54/5.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.54/5.76  thf('49', plain,
% 5.54/5.76      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0))),
% 5.54/5.76      inference('demod', [status(thm)], ['47', '48'])).
% 5.54/5.76  thf('50', plain,
% 5.54/5.76      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))),
% 5.54/5.76      inference('sup+', [status(thm)], ['34', '49'])).
% 5.54/5.76  thf('51', plain,
% 5.54/5.76      (![X8 : $i, X9 : $i]:
% 5.54/5.76         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 5.54/5.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.54/5.76  thf('52', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))
% 5.54/5.76           = (k2_xboole_0 @ X0 @ sk_A))),
% 5.54/5.76      inference('sup-', [status(thm)], ['50', '51'])).
% 5.54/5.76  thf('53', plain,
% 5.54/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.54/5.76           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.54/5.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.54/5.76  thf('54', plain,
% 5.54/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.54/5.76           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.54/5.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.54/5.76  thf('55', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 5.54/5.76           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 5.54/5.76      inference('sup+', [status(thm)], ['53', '54'])).
% 5.54/5.76  thf('56', plain,
% 5.54/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.54/5.76           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.54/5.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.54/5.76  thf('57', plain,
% 5.54/5.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.54/5.76           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.54/5.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.54/5.76  thf('58', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 5.54/5.76           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 5.54/5.76      inference('demod', [status(thm)], ['55', '56', '57'])).
% 5.54/5.76  thf('59', plain,
% 5.54/5.76      (![X19 : $i, X20 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 5.54/5.76      inference('cnf', [status(esa)], [t46_xboole_1])).
% 5.54/5.76  thf('60', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 5.54/5.76           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 5.54/5.76      inference('sup+', [status(thm)], ['58', '59'])).
% 5.54/5.76  thf('61', plain,
% 5.54/5.76      (![X0 : $i]:
% 5.54/5.76         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ (k2_xboole_0 @ X0 @ sk_A))
% 5.54/5.76           = (k1_xboole_0))),
% 5.54/5.76      inference('sup+', [status(thm)], ['52', '60'])).
% 5.54/5.76  thf('62', plain,
% 5.54/5.76      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) = (k1_xboole_0))),
% 5.54/5.76      inference('sup+', [status(thm)], ['33', '61'])).
% 5.54/5.76  thf('63', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.76  thf('64', plain,
% 5.54/5.76      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (k1_xboole_0))),
% 5.54/5.76      inference('demod', [status(thm)], ['62', '63'])).
% 5.54/5.76  thf(d10_xboole_0, axiom,
% 5.54/5.76    (![A:$i,B:$i]:
% 5.54/5.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.54/5.76  thf('65', plain,
% 5.54/5.76      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 5.54/5.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.54/5.76  thf('66', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 5.54/5.76      inference('simplify', [status(thm)], ['65'])).
% 5.54/5.76  thf('67', plain,
% 5.54/5.76      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.54/5.76         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 5.54/5.76          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 5.54/5.76      inference('cnf', [status(esa)], [t44_xboole_1])).
% 5.54/5.76  thf('68', plain,
% 5.54/5.76      (![X0 : $i, X1 : $i]:
% 5.54/5.76         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.54/5.76      inference('sup-', [status(thm)], ['66', '67'])).
% 5.54/5.76  thf('69', plain,
% 5.54/5.76      (![X8 : $i, X9 : $i]:
% 5.54/5.76         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 5.54/5.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.54/5.77  thf('70', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]:
% 5.54/5.77         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 5.54/5.77           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.54/5.77      inference('sup-', [status(thm)], ['68', '69'])).
% 5.54/5.77  thf('71', plain,
% 5.54/5.77      (((k2_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ 
% 5.54/5.77         (k2_xboole_0 @ sk_A @ k1_xboole_0))
% 5.54/5.77         = (k2_xboole_0 @ sk_A @ 
% 5.54/5.77            (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)))),
% 5.54/5.77      inference('sup+', [status(thm)], ['64', '70'])).
% 5.54/5.77  thf('72', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 5.54/5.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.54/5.77  thf('73', plain,
% 5.54/5.77      (![X8 : $i, X9 : $i]:
% 5.54/5.77         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 5.54/5.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.54/5.77  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.54/5.77      inference('sup-', [status(thm)], ['72', '73'])).
% 5.54/5.77  thf('75', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.77  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.54/5.77      inference('sup+', [status(thm)], ['74', '75'])).
% 5.54/5.77  thf('77', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.77  thf('78', plain,
% 5.54/5.77      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (k1_xboole_0))),
% 5.54/5.77      inference('demod', [status(thm)], ['62', '63'])).
% 5.54/5.77  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.54/5.77      inference('sup+', [status(thm)], ['74', '75'])).
% 5.54/5.77  thf('80', plain,
% 5.54/5.77      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 5.54/5.77      inference('demod', [status(thm)], ['71', '76', '77', '78', '79'])).
% 5.54/5.77  thf('81', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.54/5.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.54/5.77  thf(t7_xboole_1, axiom,
% 5.54/5.77    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.54/5.77  thf('82', plain,
% 5.54/5.77      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 5.54/5.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.54/5.77  thf('83', plain,
% 5.54/5.77      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.54/5.77         (~ (r1_tarski @ X26 @ X27)
% 5.54/5.77          | (r2_hidden @ X26 @ X28)
% 5.54/5.77          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 5.54/5.77      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.54/5.77  thf('84', plain,
% 5.54/5.77      (![X26 : $i, X27 : $i]:
% 5.54/5.77         ((r2_hidden @ X26 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X26 @ X27))),
% 5.54/5.77      inference('simplify', [status(thm)], ['83'])).
% 5.54/5.77  thf('85', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]:
% 5.54/5.77         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.54/5.77      inference('sup-', [status(thm)], ['82', '84'])).
% 5.54/5.77  thf('86', plain,
% 5.54/5.77      (![X31 : $i, X32 : $i]:
% 5.54/5.77         (~ (r2_hidden @ X31 @ X32)
% 5.54/5.77          | (m1_subset_1 @ X31 @ X32)
% 5.54/5.77          | (v1_xboole_0 @ X32))),
% 5.54/5.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.54/5.77  thf('87', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]:
% 5.54/5.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 5.54/5.77          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 5.54/5.77      inference('sup-', [status(thm)], ['85', '86'])).
% 5.54/5.77  thf('88', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 5.54/5.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 5.54/5.77  thf('89', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]:
% 5.54/5.77         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.54/5.77      inference('clc', [status(thm)], ['87', '88'])).
% 5.54/5.77  thf('90', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]:
% 5.54/5.77         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.54/5.77      inference('sup+', [status(thm)], ['81', '89'])).
% 5.54/5.77  thf('91', plain,
% 5.54/5.77      (![X34 : $i, X35 : $i]:
% 5.54/5.77         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 5.54/5.77          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 5.54/5.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.54/5.77  thf('92', plain,
% 5.54/5.77      (![X0 : $i, X1 : $i]:
% 5.54/5.77         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 5.54/5.77           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 5.54/5.77      inference('sup-', [status(thm)], ['90', '91'])).
% 5.54/5.77  thf('93', plain,
% 5.54/5.77      (((k3_subset_1 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 5.54/5.77         (k2_xboole_0 @ sk_C_1 @ sk_B))
% 5.54/5.77         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 5.54/5.77      inference('sup+', [status(thm)], ['80', '92'])).
% 5.54/5.77  thf('94', plain,
% 5.54/5.77      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 5.54/5.77      inference('demod', [status(thm)], ['71', '76', '77', '78', '79'])).
% 5.54/5.77  thf('95', plain,
% 5.54/5.77      (![X0 : $i]:
% 5.54/5.77         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 5.54/5.77           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 5.54/5.77      inference('sup+', [status(thm)], ['18', '19'])).
% 5.54/5.77  thf('96', plain,
% 5.54/5.77      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 5.54/5.77         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))),
% 5.54/5.77      inference('demod', [status(thm)], ['93', '94', '95'])).
% 5.54/5.77  thf('97', plain,
% 5.54/5.77      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 5.54/5.77        (k3_subset_1 @ sk_A @ sk_B))),
% 5.54/5.77      inference('demod', [status(thm)], ['23', '96'])).
% 5.54/5.77  thf('98', plain, ($false), inference('demod', [status(thm)], ['8', '97'])).
% 5.54/5.77  
% 5.54/5.77  % SZS output end Refutation
% 5.54/5.77  
% 5.54/5.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
