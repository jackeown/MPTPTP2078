%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0678+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9YMtEjjEBV

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:18 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 167 expanded)
%              Number of leaves         :   29 (  60 expanded)
%              Depth                    :   25
%              Number of atoms          :  912 (1706 expanded)
%              Number of equality atoms :   71 ( 119 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t122_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i,C: $i] :
            ( ( k9_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) )
            = ( k3_xboole_0 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ! [B: $i,C: $i] :
              ( ( k9_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) )
              = ( k3_xboole_0 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t122_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_B @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k11_relat_1 @ X17 @ X16 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( ( k1_funct_1 @ X7 @ ( sk_B @ X7 ) )
        = ( k1_funct_1 @ X7 @ ( sk_C @ X7 ) ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_C @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k11_relat_1 @ X17 @ X16 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_A @ X21 ) @ ( k9_relat_1 @ sk_A @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_A @ X21 ) @ ( k9_relat_1 @ sk_A @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k9_relat_1 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( k9_relat_1 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k9_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1 = X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['15','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['14','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( ( sk_C @ sk_A )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['13','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( ( sk_C @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A )
        = X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A )
        = X0 )
      | ( ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('54',plain,
    ( ( k1_xboole_0
      = ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('56',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['61'])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ( r1_subset_1 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('64',plain,
    ( ( r1_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(irreflexivity_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( r1_subset_1 @ A @ A ) ) )).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_subset_1 @ X12 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r1_subset_1])).

thf('67',plain,
    ( ! [X12: $i] :
        ( ~ ( r1_subset_1 @ X12 @ X12 )
        | ( v1_xboole_0 @ X12 ) )
   <= ! [X12: $i] :
        ( ~ ( r1_subset_1 @ X12 @ X12 )
        | ( v1_xboole_0 @ X12 ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ! [X13: $i] :
        ( v1_xboole_0 @ X13 )
   <= ! [X13: $i] :
        ( v1_xboole_0 @ X13 ) ),
    inference(split,[status(esa)],['66'])).

thf('69',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('70',plain,(
    ~ ! [X13: $i] :
        ( v1_xboole_0 @ X13 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X12: $i] :
        ( ~ ( r1_subset_1 @ X12 @ X12 )
        | ( v1_xboole_0 @ X12 ) )
    | ! [X13: $i] :
        ( v1_xboole_0 @ X13 ) ),
    inference(split,[status(esa)],['66'])).

thf('72',plain,(
    ! [X12: $i] :
      ( ~ ( r1_subset_1 @ X12 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X12: $i] :
      ( ~ ( r1_subset_1 @ X12 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(simpl_trail,[status(thm)],['67','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['65','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','74','75','76'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_C @ sk_A )
    = ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i] :
      ( ( ( sk_B @ X7 )
       != ( sk_C @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('81',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85'])).


%------------------------------------------------------------------------------
