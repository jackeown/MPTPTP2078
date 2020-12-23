%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9WlAzBU8lB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:57 EST 2020

% Result     : Theorem 12.93s
% Output     : Refutation 12.93s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 477 expanded)
%              Number of leaves         :   34 ( 160 expanded)
%              Depth                    :   20
%              Number of atoms          : 1001 (3586 expanded)
%              Number of equality atoms :   60 ( 294 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X51: $i] :
      ( ( ( k3_relat_1 @ X51 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X51: $i] :
      ( ( ( k3_relat_1 @ X51 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X53 ) @ ( k1_relat_1 @ X52 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X53 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X53 ) @ ( k1_relat_1 @ X52 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X53 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('27',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42
        = ( k1_relat_1 @ X39 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X42 @ X39 ) @ ( sk_D @ X42 @ X39 ) ) @ X39 )
      | ( r2_hidden @ ( sk_C @ X42 @ X39 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X31: $i] :
      ( ( k2_zfmisc_1 @ X31 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('34',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('37',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','34','35','36','37','38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('56',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('64',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X51: $i] :
      ( ( ( k3_relat_1 @ X51 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('67',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('80',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X55 ) @ ( k2_relat_1 @ X54 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X55 @ X54 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('81',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('82',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('83',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X55 ) @ ( k2_relat_1 @ X54 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X55 @ X54 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('87',plain,(
    ! [X46: $i,X49: $i] :
      ( ( X49
        = ( k2_relat_1 @ X46 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X49 @ X46 ) @ ( sk_C_1 @ X49 @ X46 ) ) @ X46 )
      | ( r2_hidden @ ( sk_C_1 @ X49 @ X46 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('95',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','91','92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','101'])).

thf('103',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('104',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9WlAzBU8lB
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 12.93/13.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.93/13.18  % Solved by: fo/fo7.sh
% 12.93/13.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.93/13.18  % done 19269 iterations in 12.709s
% 12.93/13.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.93/13.18  % SZS output start Refutation
% 12.93/13.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.93/13.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.93/13.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.93/13.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.93/13.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.93/13.18  thf(sk_A_type, type, sk_A: $i).
% 12.93/13.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.93/13.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.93/13.18  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 12.93/13.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.93/13.18  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 12.93/13.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.93/13.18  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 12.93/13.18  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 12.93/13.18  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 12.93/13.18  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 12.93/13.18  thf(sk_B_1_type, type, sk_B_1: $i).
% 12.93/13.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.93/13.18  thf(t31_relat_1, conjecture,
% 12.93/13.18    (![A:$i]:
% 12.93/13.18     ( ( v1_relat_1 @ A ) =>
% 12.93/13.18       ( ![B:$i]:
% 12.93/13.18         ( ( v1_relat_1 @ B ) =>
% 12.93/13.18           ( ( r1_tarski @ A @ B ) =>
% 12.93/13.18             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 12.93/13.18  thf(zf_stmt_0, negated_conjecture,
% 12.93/13.18    (~( ![A:$i]:
% 12.93/13.18        ( ( v1_relat_1 @ A ) =>
% 12.93/13.18          ( ![B:$i]:
% 12.93/13.18            ( ( v1_relat_1 @ B ) =>
% 12.93/13.18              ( ( r1_tarski @ A @ B ) =>
% 12.93/13.18                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 12.93/13.18    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 12.93/13.18  thf('0', plain,
% 12.93/13.18      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf(d6_relat_1, axiom,
% 12.93/13.18    (![A:$i]:
% 12.93/13.18     ( ( v1_relat_1 @ A ) =>
% 12.93/13.18       ( ( k3_relat_1 @ A ) =
% 12.93/13.18         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 12.93/13.18  thf('1', plain,
% 12.93/13.18      (![X51 : $i]:
% 12.93/13.18         (((k3_relat_1 @ X51)
% 12.93/13.18            = (k2_xboole_0 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51)))
% 12.93/13.18          | ~ (v1_relat_1 @ X51))),
% 12.93/13.18      inference('cnf', [status(esa)], [d6_relat_1])).
% 12.93/13.18  thf('2', plain,
% 12.93/13.18      (![X51 : $i]:
% 12.93/13.18         (((k3_relat_1 @ X51)
% 12.93/13.18            = (k2_xboole_0 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51)))
% 12.93/13.18          | ~ (v1_relat_1 @ X51))),
% 12.93/13.18      inference('cnf', [status(esa)], [d6_relat_1])).
% 12.93/13.18  thf(d10_xboole_0, axiom,
% 12.93/13.18    (![A:$i,B:$i]:
% 12.93/13.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.93/13.18  thf('3', plain,
% 12.93/13.18      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 12.93/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.93/13.18  thf('4', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 12.93/13.18      inference('simplify', [status(thm)], ['3'])).
% 12.93/13.18  thf(l32_xboole_1, axiom,
% 12.93/13.18    (![A:$i,B:$i]:
% 12.93/13.18     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.93/13.18  thf('5', plain,
% 12.93/13.18      (![X5 : $i, X7 : $i]:
% 12.93/13.18         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 12.93/13.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 12.93/13.18  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['4', '5'])).
% 12.93/13.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 12.93/13.18  thf('7', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 12.93/13.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.93/13.18  thf('8', plain,
% 12.93/13.18      (![X5 : $i, X7 : $i]:
% 12.93/13.18         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 12.93/13.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 12.93/13.18  thf('9', plain,
% 12.93/13.18      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['7', '8'])).
% 12.93/13.18  thf('10', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 12.93/13.18      inference('sup+', [status(thm)], ['6', '9'])).
% 12.93/13.18  thf(t41_xboole_1, axiom,
% 12.93/13.18    (![A:$i,B:$i,C:$i]:
% 12.93/13.18     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 12.93/13.18       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 12.93/13.18  thf('11', plain,
% 12.93/13.18      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.93/13.18         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 12.93/13.18           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 12.93/13.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.93/13.18  thf('12', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 12.93/13.18      inference('demod', [status(thm)], ['10', '11'])).
% 12.93/13.18  thf('13', plain,
% 12.93/13.18      (![X5 : $i, X6 : $i]:
% 12.93/13.18         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 12.93/13.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 12.93/13.18  thf('14', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         (((k1_xboole_0) != (k1_xboole_0))
% 12.93/13.18          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.93/13.18      inference('sup-', [status(thm)], ['12', '13'])).
% 12.93/13.18  thf('15', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 12.93/13.18      inference('simplify', [status(thm)], ['14'])).
% 12.93/13.18  thf('16', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 12.93/13.18          | ~ (v1_relat_1 @ X0))),
% 12.93/13.18      inference('sup+', [status(thm)], ['2', '15'])).
% 12.93/13.18  thf('17', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('18', plain,
% 12.93/13.18      (![X5 : $i, X7 : $i]:
% 12.93/13.18         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 12.93/13.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 12.93/13.18  thf('19', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['17', '18'])).
% 12.93/13.18  thf(t15_relat_1, axiom,
% 12.93/13.18    (![A:$i]:
% 12.93/13.18     ( ( v1_relat_1 @ A ) =>
% 12.93/13.18       ( ![B:$i]:
% 12.93/13.18         ( ( v1_relat_1 @ B ) =>
% 12.93/13.18           ( r1_tarski @
% 12.93/13.18             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 12.93/13.18             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 12.93/13.18  thf('20', plain,
% 12.93/13.18      (![X52 : $i, X53 : $i]:
% 12.93/13.18         (~ (v1_relat_1 @ X52)
% 12.93/13.18          | (r1_tarski @ 
% 12.93/13.18             (k6_subset_1 @ (k1_relat_1 @ X53) @ (k1_relat_1 @ X52)) @ 
% 12.93/13.18             (k1_relat_1 @ (k6_subset_1 @ X53 @ X52)))
% 12.93/13.18          | ~ (v1_relat_1 @ X53))),
% 12.93/13.18      inference('cnf', [status(esa)], [t15_relat_1])).
% 12.93/13.18  thf(redefinition_k6_subset_1, axiom,
% 12.93/13.18    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 12.93/13.18  thf('21', plain,
% 12.93/13.18      (![X35 : $i, X36 : $i]:
% 12.93/13.18         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 12.93/13.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.93/13.18  thf('22', plain,
% 12.93/13.18      (![X35 : $i, X36 : $i]:
% 12.93/13.18         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 12.93/13.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.93/13.18  thf('23', plain,
% 12.93/13.18      (![X52 : $i, X53 : $i]:
% 12.93/13.18         (~ (v1_relat_1 @ X52)
% 12.93/13.18          | (r1_tarski @ 
% 12.93/13.18             (k4_xboole_0 @ (k1_relat_1 @ X53) @ (k1_relat_1 @ X52)) @ 
% 12.93/13.18             (k1_relat_1 @ (k4_xboole_0 @ X53 @ X52)))
% 12.93/13.18          | ~ (v1_relat_1 @ X53))),
% 12.93/13.18      inference('demod', [status(thm)], ['20', '21', '22'])).
% 12.93/13.18  thf('24', plain,
% 12.93/13.18      (![X2 : $i, X4 : $i]:
% 12.93/13.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 12.93/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.93/13.18  thf('25', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         (~ (v1_relat_1 @ X1)
% 12.93/13.18          | ~ (v1_relat_1 @ X0)
% 12.93/13.18          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 12.93/13.18               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 12.93/13.18          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 12.93/13.18              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 12.93/13.18      inference('sup-', [status(thm)], ['23', '24'])).
% 12.93/13.18  thf('26', plain,
% 12.93/13.18      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 12.93/13.18           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 12.93/13.18        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 12.93/13.18            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 12.93/13.18        | ~ (v1_relat_1 @ sk_B_1)
% 12.93/13.18        | ~ (v1_relat_1 @ sk_A))),
% 12.93/13.18      inference('sup-', [status(thm)], ['19', '25'])).
% 12.93/13.18  thf(d4_relat_1, axiom,
% 12.93/13.18    (![A:$i,B:$i]:
% 12.93/13.18     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 12.93/13.18       ( ![C:$i]:
% 12.93/13.18         ( ( r2_hidden @ C @ B ) <=>
% 12.93/13.18           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 12.93/13.18  thf('27', plain,
% 12.93/13.18      (![X39 : $i, X42 : $i]:
% 12.93/13.18         (((X42) = (k1_relat_1 @ X39))
% 12.93/13.18          | (r2_hidden @ 
% 12.93/13.18             (k4_tarski @ (sk_C @ X42 @ X39) @ (sk_D @ X42 @ X39)) @ X39)
% 12.93/13.18          | (r2_hidden @ (sk_C @ X42 @ X39) @ X42))),
% 12.93/13.18      inference('cnf', [status(esa)], [d4_relat_1])).
% 12.93/13.18  thf(t113_zfmisc_1, axiom,
% 12.93/13.18    (![A:$i,B:$i]:
% 12.93/13.18     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 12.93/13.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 12.93/13.18  thf('28', plain,
% 12.93/13.18      (![X31 : $i, X32 : $i]:
% 12.93/13.18         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 12.93/13.18          | ((X32) != (k1_xboole_0)))),
% 12.93/13.18      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 12.93/13.18  thf('29', plain,
% 12.93/13.18      (![X31 : $i]: ((k2_zfmisc_1 @ X31 @ k1_xboole_0) = (k1_xboole_0))),
% 12.93/13.18      inference('simplify', [status(thm)], ['28'])).
% 12.93/13.18  thf(t152_zfmisc_1, axiom,
% 12.93/13.18    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 12.93/13.18  thf('30', plain,
% 12.93/13.18      (![X33 : $i, X34 : $i]: ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X33 @ X34))),
% 12.93/13.18      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 12.93/13.18  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.93/13.18      inference('sup-', [status(thm)], ['29', '30'])).
% 12.93/13.18  thf('32', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 12.93/13.18          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 12.93/13.18      inference('sup-', [status(thm)], ['27', '31'])).
% 12.93/13.18  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.93/13.18      inference('sup-', [status(thm)], ['29', '30'])).
% 12.93/13.18  thf('34', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['32', '33'])).
% 12.93/13.18  thf('35', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 12.93/13.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.93/13.18  thf('36', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['17', '18'])).
% 12.93/13.18  thf('37', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['32', '33'])).
% 12.93/13.18  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('40', plain,
% 12.93/13.18      (((k1_xboole_0)
% 12.93/13.18         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 12.93/13.18      inference('demod', [status(thm)],
% 12.93/13.18                ['26', '34', '35', '36', '37', '38', '39'])).
% 12.93/13.18  thf('41', plain,
% 12.93/13.18      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.93/13.18         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 12.93/13.18           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 12.93/13.18      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.93/13.18  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['4', '5'])).
% 12.93/13.18  thf('43', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 12.93/13.18           = (k1_xboole_0))),
% 12.93/13.18      inference('sup+', [status(thm)], ['41', '42'])).
% 12.93/13.18  thf('44', plain,
% 12.93/13.18      (![X5 : $i, X6 : $i]:
% 12.93/13.18         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 12.93/13.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 12.93/13.18  thf('45', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         (((k1_xboole_0) != (k1_xboole_0))
% 12.93/13.18          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 12.93/13.18      inference('sup-', [status(thm)], ['43', '44'])).
% 12.93/13.18  thf('46', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.93/13.18      inference('simplify', [status(thm)], ['45'])).
% 12.93/13.18  thf(t1_xboole_1, axiom,
% 12.93/13.18    (![A:$i,B:$i,C:$i]:
% 12.93/13.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 12.93/13.18       ( r1_tarski @ A @ C ) ))).
% 12.93/13.18  thf('47', plain,
% 12.93/13.18      (![X11 : $i, X12 : $i, X13 : $i]:
% 12.93/13.18         (~ (r1_tarski @ X11 @ X12)
% 12.93/13.18          | ~ (r1_tarski @ X12 @ X13)
% 12.93/13.18          | (r1_tarski @ X11 @ X13))),
% 12.93/13.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.93/13.18  thf('48', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.93/13.18         ((r1_tarski @ X1 @ X2)
% 12.93/13.18          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 12.93/13.18      inference('sup-', [status(thm)], ['46', '47'])).
% 12.93/13.18  thf('49', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         (~ (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 12.93/13.18             X0)
% 12.93/13.18          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['40', '48'])).
% 12.93/13.18  thf('50', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 12.93/13.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.93/13.18  thf('51', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 12.93/13.18      inference('simplify', [status(thm)], ['3'])).
% 12.93/13.18  thf(t8_xboole_1, axiom,
% 12.93/13.18    (![A:$i,B:$i,C:$i]:
% 12.93/13.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 12.93/13.18       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 12.93/13.18  thf('52', plain,
% 12.93/13.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 12.93/13.18         (~ (r1_tarski @ X20 @ X21)
% 12.93/13.18          | ~ (r1_tarski @ X22 @ X21)
% 12.93/13.18          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 12.93/13.18      inference('cnf', [status(esa)], [t8_xboole_1])).
% 12.93/13.18  thf('53', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['51', '52'])).
% 12.93/13.18  thf('54', plain,
% 12.93/13.18      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 12.93/13.18      inference('sup-', [status(thm)], ['50', '53'])).
% 12.93/13.18  thf('55', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 12.93/13.18      inference('simplify', [status(thm)], ['14'])).
% 12.93/13.18  thf('56', plain,
% 12.93/13.18      (![X2 : $i, X4 : $i]:
% 12.93/13.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 12.93/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.93/13.18  thf('57', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.93/13.18          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 12.93/13.18      inference('sup-', [status(thm)], ['55', '56'])).
% 12.93/13.18  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['54', '57'])).
% 12.93/13.18  thf('59', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 12.93/13.18          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 12.93/13.18      inference('demod', [status(thm)], ['49', '58'])).
% 12.93/13.18  thf('60', plain,
% 12.93/13.18      ((~ (v1_relat_1 @ sk_B_1)
% 12.93/13.18        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 12.93/13.18      inference('sup-', [status(thm)], ['16', '59'])).
% 12.93/13.18  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('demod', [status(thm)], ['60', '61'])).
% 12.93/13.18  thf('63', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['51', '52'])).
% 12.93/13.18  thf('64', plain,
% 12.93/13.18      ((r1_tarski @ 
% 12.93/13.18        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 12.93/13.18        (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('sup-', [status(thm)], ['62', '63'])).
% 12.93/13.18  thf('65', plain,
% 12.93/13.18      (![X51 : $i]:
% 12.93/13.18         (((k3_relat_1 @ X51)
% 12.93/13.18            = (k2_xboole_0 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51)))
% 12.93/13.18          | ~ (v1_relat_1 @ X51))),
% 12.93/13.18      inference('cnf', [status(esa)], [d6_relat_1])).
% 12.93/13.18  thf('66', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 12.93/13.18      inference('simplify', [status(thm)], ['14'])).
% 12.93/13.18  thf('67', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 12.93/13.18      inference('simplify', [status(thm)], ['3'])).
% 12.93/13.18  thf(t10_xboole_1, axiom,
% 12.93/13.18    (![A:$i,B:$i,C:$i]:
% 12.93/13.18     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 12.93/13.18  thf('68', plain,
% 12.93/13.18      (![X8 : $i, X9 : $i, X10 : $i]:
% 12.93/13.18         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 12.93/13.18      inference('cnf', [status(esa)], [t10_xboole_1])).
% 12.93/13.18  thf('69', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['67', '68'])).
% 12.93/13.18  thf('70', plain,
% 12.93/13.18      (![X11 : $i, X12 : $i, X13 : $i]:
% 12.93/13.18         (~ (r1_tarski @ X11 @ X12)
% 12.93/13.18          | ~ (r1_tarski @ X12 @ X13)
% 12.93/13.18          | (r1_tarski @ X11 @ X13))),
% 12.93/13.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.93/13.18  thf('71', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.93/13.18         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 12.93/13.18      inference('sup-', [status(thm)], ['69', '70'])).
% 12.93/13.18  thf('72', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.93/13.18         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['66', '71'])).
% 12.93/13.18  thf('73', plain,
% 12.93/13.18      (![X11 : $i, X12 : $i, X13 : $i]:
% 12.93/13.18         (~ (r1_tarski @ X11 @ X12)
% 12.93/13.18          | ~ (r1_tarski @ X12 @ X13)
% 12.93/13.18          | (r1_tarski @ X11 @ X13))),
% 12.93/13.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.93/13.18  thf('74', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.93/13.18         ((r1_tarski @ X1 @ X3)
% 12.93/13.18          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3))),
% 12.93/13.18      inference('sup-', [status(thm)], ['72', '73'])).
% 12.93/13.18  thf('75', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.93/13.18         (~ (r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ X2) @ X1)
% 12.93/13.18          | ~ (v1_relat_1 @ X0)
% 12.93/13.18          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 12.93/13.18      inference('sup-', [status(thm)], ['65', '74'])).
% 12.93/13.18  thf('76', plain,
% 12.93/13.18      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 12.93/13.18        | ~ (v1_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('sup-', [status(thm)], ['64', '75'])).
% 12.93/13.18  thf('77', plain, ((v1_relat_1 @ sk_B_1)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('78', plain,
% 12.93/13.18      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('demod', [status(thm)], ['76', '77'])).
% 12.93/13.18  thf('79', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['17', '18'])).
% 12.93/13.18  thf(t28_relat_1, axiom,
% 12.93/13.18    (![A:$i]:
% 12.93/13.18     ( ( v1_relat_1 @ A ) =>
% 12.93/13.18       ( ![B:$i]:
% 12.93/13.18         ( ( v1_relat_1 @ B ) =>
% 12.93/13.18           ( r1_tarski @
% 12.93/13.18             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 12.93/13.18             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 12.93/13.18  thf('80', plain,
% 12.93/13.18      (![X54 : $i, X55 : $i]:
% 12.93/13.18         (~ (v1_relat_1 @ X54)
% 12.93/13.18          | (r1_tarski @ 
% 12.93/13.18             (k6_subset_1 @ (k2_relat_1 @ X55) @ (k2_relat_1 @ X54)) @ 
% 12.93/13.18             (k2_relat_1 @ (k6_subset_1 @ X55 @ X54)))
% 12.93/13.18          | ~ (v1_relat_1 @ X55))),
% 12.93/13.18      inference('cnf', [status(esa)], [t28_relat_1])).
% 12.93/13.18  thf('81', plain,
% 12.93/13.18      (![X35 : $i, X36 : $i]:
% 12.93/13.18         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 12.93/13.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.93/13.18  thf('82', plain,
% 12.93/13.18      (![X35 : $i, X36 : $i]:
% 12.93/13.18         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 12.93/13.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.93/13.18  thf('83', plain,
% 12.93/13.18      (![X54 : $i, X55 : $i]:
% 12.93/13.18         (~ (v1_relat_1 @ X54)
% 12.93/13.18          | (r1_tarski @ 
% 12.93/13.18             (k4_xboole_0 @ (k2_relat_1 @ X55) @ (k2_relat_1 @ X54)) @ 
% 12.93/13.18             (k2_relat_1 @ (k4_xboole_0 @ X55 @ X54)))
% 12.93/13.18          | ~ (v1_relat_1 @ X55))),
% 12.93/13.18      inference('demod', [status(thm)], ['80', '81', '82'])).
% 12.93/13.18  thf('84', plain,
% 12.93/13.18      (![X2 : $i, X4 : $i]:
% 12.93/13.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 12.93/13.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.93/13.18  thf('85', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i]:
% 12.93/13.18         (~ (v1_relat_1 @ X1)
% 12.93/13.18          | ~ (v1_relat_1 @ X0)
% 12.93/13.18          | ~ (r1_tarski @ (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 12.93/13.18               (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 12.93/13.18          | ((k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 12.93/13.18              = (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))),
% 12.93/13.18      inference('sup-', [status(thm)], ['83', '84'])).
% 12.93/13.18  thf('86', plain,
% 12.93/13.18      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 12.93/13.18           (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 12.93/13.18        | ((k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 12.93/13.18            = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 12.93/13.18        | ~ (v1_relat_1 @ sk_B_1)
% 12.93/13.18        | ~ (v1_relat_1 @ sk_A))),
% 12.93/13.18      inference('sup-', [status(thm)], ['79', '85'])).
% 12.93/13.18  thf(d5_relat_1, axiom,
% 12.93/13.18    (![A:$i,B:$i]:
% 12.93/13.18     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 12.93/13.18       ( ![C:$i]:
% 12.93/13.18         ( ( r2_hidden @ C @ B ) <=>
% 12.93/13.18           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 12.93/13.18  thf('87', plain,
% 12.93/13.18      (![X46 : $i, X49 : $i]:
% 12.93/13.18         (((X49) = (k2_relat_1 @ X46))
% 12.93/13.18          | (r2_hidden @ 
% 12.93/13.18             (k4_tarski @ (sk_D_2 @ X49 @ X46) @ (sk_C_1 @ X49 @ X46)) @ X46)
% 12.93/13.18          | (r2_hidden @ (sk_C_1 @ X49 @ X46) @ X49))),
% 12.93/13.18      inference('cnf', [status(esa)], [d5_relat_1])).
% 12.93/13.18  thf('88', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.93/13.18      inference('sup-', [status(thm)], ['29', '30'])).
% 12.93/13.18  thf('89', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 12.93/13.18          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 12.93/13.18      inference('sup-', [status(thm)], ['87', '88'])).
% 12.93/13.18  thf('90', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.93/13.18      inference('sup-', [status(thm)], ['29', '30'])).
% 12.93/13.18  thf('91', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['89', '90'])).
% 12.93/13.18  thf('92', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 12.93/13.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.93/13.18  thf('93', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['17', '18'])).
% 12.93/13.18  thf('94', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['89', '90'])).
% 12.93/13.18  thf('95', plain, ((v1_relat_1 @ sk_B_1)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('97', plain,
% 12.93/13.18      (((k1_xboole_0)
% 12.93/13.18         = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 12.93/13.18      inference('demod', [status(thm)],
% 12.93/13.18                ['86', '91', '92', '93', '94', '95', '96'])).
% 12.93/13.18  thf('98', plain,
% 12.93/13.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.93/13.18         ((r1_tarski @ X1 @ X2)
% 12.93/13.18          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 12.93/13.18      inference('sup-', [status(thm)], ['46', '47'])).
% 12.93/13.18  thf('99', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         (~ (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 12.93/13.18             X0)
% 12.93/13.18          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['97', '98'])).
% 12.93/13.18  thf('100', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 12.93/13.18      inference('sup-', [status(thm)], ['54', '57'])).
% 12.93/13.18  thf('101', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         (~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0)
% 12.93/13.18          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 12.93/13.18      inference('demod', [status(thm)], ['99', '100'])).
% 12.93/13.18  thf('102', plain,
% 12.93/13.18      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('sup-', [status(thm)], ['78', '101'])).
% 12.93/13.18  thf('103', plain,
% 12.93/13.18      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('demod', [status(thm)], ['60', '61'])).
% 12.93/13.18  thf('104', plain,
% 12.93/13.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 12.93/13.18         (~ (r1_tarski @ X20 @ X21)
% 12.93/13.18          | ~ (r1_tarski @ X22 @ X21)
% 12.93/13.18          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 12.93/13.18      inference('cnf', [status(esa)], [t8_xboole_1])).
% 12.93/13.18  thf('105', plain,
% 12.93/13.18      (![X0 : $i]:
% 12.93/13.18         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 12.93/13.18           (k3_relat_1 @ sk_B_1))
% 12.93/13.18          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 12.93/13.18      inference('sup-', [status(thm)], ['103', '104'])).
% 12.93/13.18  thf('106', plain,
% 12.93/13.18      ((r1_tarski @ 
% 12.93/13.18        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 12.93/13.18        (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('sup-', [status(thm)], ['102', '105'])).
% 12.93/13.18  thf('107', plain,
% 12.93/13.18      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 12.93/13.18        | ~ (v1_relat_1 @ sk_A))),
% 12.93/13.18      inference('sup+', [status(thm)], ['1', '106'])).
% 12.93/13.18  thf('108', plain, ((v1_relat_1 @ sk_A)),
% 12.93/13.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.93/13.18  thf('109', plain,
% 12.93/13.18      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 12.93/13.18      inference('demod', [status(thm)], ['107', '108'])).
% 12.93/13.18  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 12.93/13.18  
% 12.93/13.18  % SZS output end Refutation
% 12.93/13.18  
% 12.93/13.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
