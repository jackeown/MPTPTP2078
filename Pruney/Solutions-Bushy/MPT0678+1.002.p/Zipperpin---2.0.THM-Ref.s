%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0678+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eg18E79dTR

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:18 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 138 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   19
%              Number of atoms          :  751 (1456 expanded)
%              Number of equality atoms :   65 ( 108 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k11_relat_1 @ X13 @ X12 )
        = ( k1_tarski @ ( k1_funct_1 @ X13 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k11_relat_1 @ X13 @ X12 )
        = ( k1_tarski @ ( k1_funct_1 @ X13 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_A @ X19 ) @ ( k9_relat_1 @ sk_A @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_A @ X19 ) @ ( k9_relat_1 @ sk_A @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k9_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( X0
        = ( sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['13','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( X0
        = ( sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C @ sk_A ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('43',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('50',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('51',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('52',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','54','55'])).

thf('57',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i] :
      ( ( ( sk_B @ X7 )
       != ( sk_C @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('60',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).


%------------------------------------------------------------------------------
