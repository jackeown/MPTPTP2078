%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x6Acm5zMd5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:53 EST 2020

% Result     : Theorem 36.56s
% Output     : Refutation 36.56s
% Verified   : 
% Statistics : Number of formulae       :  263 (1073 expanded)
%              Number of leaves         :   48 ( 363 expanded)
%              Depth                    :   26
%              Number of atoms          : 1777 (7967 expanded)
%              Number of equality atoms :  116 ( 521 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v1_relat_1 @ X61 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X62 ) @ ( k2_relat_1 @ X61 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X62 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v1_relat_1 @ X61 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X62 ) @ ( k2_relat_1 @ X61 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X62 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X48: $i] :
      ( ( v1_relat_1 @ X48 )
      | ~ ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('14',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X53 @ X52 )
      | ( r2_hidden @ ( k4_tarski @ X53 @ ( sk_D_1 @ X53 @ X51 ) ) @ X51 )
      | ( X52
       != ( k1_relat_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('15',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X53 @ ( sk_D_1 @ X53 @ X51 ) ) @ X51 )
      | ~ ( r2_hidden @ X53 @ ( k1_relat_1 @ X51 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('24',plain,(
    ! [X34: $i] :
      ( r1_xboole_0 @ X34 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('34',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_tarski @ X39 @ X38 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X37 @ X36 )
      | ( r1_tarski @ ( k2_xboole_0 @ X35 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','51'])).

thf('53',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k3_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','56'])).

thf('58',plain,(
    ! [X48: $i] :
      ( ( v1_relat_1 @ X48 )
      | ~ ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('61',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X59 ) @ ( k1_relat_1 @ X59 ) )
      | ~ ( r2_hidden @ X60 @ ( k2_relat_1 @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_3 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('64',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('68',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('76',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('82',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('94',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X58 ) @ ( k1_relat_1 @ X57 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X58 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf('95',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('96',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('97',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X58 ) @ ( k1_relat_1 @ X57 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X58 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('102',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('104',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105','106'])).

thf('108',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('109',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_tarski @ X39 @ X38 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('113',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('118',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['116','123'])).

thf('125',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['111','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('127',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('134',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('136',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('141',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('143',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('145',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['141','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['116','123'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','155'])).

thf('157',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('158',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X37 @ X36 )
      | ( r1_tarski @ ( k2_xboole_0 @ X35 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('162',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('163',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('164',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('165',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['163','166'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('168',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ X29 @ ( k2_xboole_0 @ X30 @ X31 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['162','171'])).

thf('173',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['161','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('177',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('179',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('184',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['185','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['184','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('198',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
      = ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('200',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('201',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('202',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X16 @ ( k2_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['200','203'])).

thf('205',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X37 @ X36 )
      | ( r1_tarski @ ( k2_xboole_0 @ X35 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('209',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['198','210'])).

thf('212',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['160','211'])).

thf('213',plain,(
    $false ),
    inference(demod,[status(thm)],['0','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x6Acm5zMd5
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 36.56/36.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.56/36.80  % Solved by: fo/fo7.sh
% 36.56/36.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.56/36.80  % done 44263 iterations in 36.362s
% 36.56/36.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.56/36.80  % SZS output start Refutation
% 36.56/36.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 36.56/36.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 36.56/36.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 36.56/36.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.56/36.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 36.56/36.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 36.56/36.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 36.56/36.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 36.56/36.80  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 36.56/36.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 36.56/36.80  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 36.56/36.80  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 36.56/36.80  thf(sk_A_type, type, sk_A: $i).
% 36.56/36.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.56/36.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 36.56/36.80  thf(sk_B_type, type, sk_B: $i).
% 36.56/36.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 36.56/36.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 36.56/36.80  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 36.56/36.80  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 36.56/36.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 36.56/36.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 36.56/36.80  thf(t31_relat_1, conjecture,
% 36.56/36.80    (![A:$i]:
% 36.56/36.80     ( ( v1_relat_1 @ A ) =>
% 36.56/36.80       ( ![B:$i]:
% 36.56/36.80         ( ( v1_relat_1 @ B ) =>
% 36.56/36.80           ( ( r1_tarski @ A @ B ) =>
% 36.56/36.80             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 36.56/36.80  thf(zf_stmt_0, negated_conjecture,
% 36.56/36.80    (~( ![A:$i]:
% 36.56/36.80        ( ( v1_relat_1 @ A ) =>
% 36.56/36.80          ( ![B:$i]:
% 36.56/36.80            ( ( v1_relat_1 @ B ) =>
% 36.56/36.80              ( ( r1_tarski @ A @ B ) =>
% 36.56/36.80                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 36.56/36.80    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 36.56/36.80  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf(l32_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.56/36.80  thf('2', plain,
% 36.56/36.80      (![X13 : $i, X15 : $i]:
% 36.56/36.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.56/36.80          | ~ (r1_tarski @ X13 @ X15))),
% 36.56/36.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.56/36.80  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['1', '2'])).
% 36.56/36.80  thf(t28_relat_1, axiom,
% 36.56/36.80    (![A:$i]:
% 36.56/36.80     ( ( v1_relat_1 @ A ) =>
% 36.56/36.80       ( ![B:$i]:
% 36.56/36.80         ( ( v1_relat_1 @ B ) =>
% 36.56/36.80           ( r1_tarski @
% 36.56/36.80             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 36.56/36.80             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 36.56/36.80  thf('4', plain,
% 36.56/36.80      (![X61 : $i, X62 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X61)
% 36.56/36.80          | (r1_tarski @ 
% 36.56/36.80             (k6_subset_1 @ (k2_relat_1 @ X62) @ (k2_relat_1 @ X61)) @ 
% 36.56/36.80             (k2_relat_1 @ (k6_subset_1 @ X62 @ X61)))
% 36.56/36.80          | ~ (v1_relat_1 @ X62))),
% 36.56/36.80      inference('cnf', [status(esa)], [t28_relat_1])).
% 36.56/36.80  thf(redefinition_k6_subset_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 36.56/36.80  thf('5', plain,
% 36.56/36.80      (![X44 : $i, X45 : $i]:
% 36.56/36.80         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 36.56/36.80      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 36.56/36.80  thf('6', plain,
% 36.56/36.80      (![X44 : $i, X45 : $i]:
% 36.56/36.80         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 36.56/36.80      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 36.56/36.80  thf('7', plain,
% 36.56/36.80      (![X61 : $i, X62 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X61)
% 36.56/36.80          | (r1_tarski @ 
% 36.56/36.80             (k4_xboole_0 @ (k2_relat_1 @ X62) @ (k2_relat_1 @ X61)) @ 
% 36.56/36.80             (k2_relat_1 @ (k4_xboole_0 @ X62 @ X61)))
% 36.56/36.80          | ~ (v1_relat_1 @ X62))),
% 36.56/36.80      inference('demod', [status(thm)], ['4', '5', '6'])).
% 36.56/36.80  thf('8', plain,
% 36.56/36.80      (((r1_tarski @ 
% 36.56/36.80         (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 36.56/36.80         (k2_relat_1 @ k1_xboole_0))
% 36.56/36.80        | ~ (v1_relat_1 @ sk_A)
% 36.56/36.80        | ~ (v1_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup+', [status(thm)], ['3', '7'])).
% 36.56/36.80  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('11', plain,
% 36.56/36.80      ((r1_tarski @ 
% 36.56/36.80        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 36.56/36.80        (k2_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('demod', [status(thm)], ['8', '9', '10'])).
% 36.56/36.80  thf(cc1_relat_1, axiom,
% 36.56/36.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 36.56/36.80  thf('12', plain, (![X48 : $i]: ((v1_relat_1 @ X48) | ~ (v1_xboole_0 @ X48))),
% 36.56/36.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 36.56/36.80  thf(d3_tarski, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( r1_tarski @ A @ B ) <=>
% 36.56/36.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 36.56/36.80  thf('13', plain,
% 36.56/36.80      (![X1 : $i, X3 : $i]:
% 36.56/36.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 36.56/36.80      inference('cnf', [status(esa)], [d3_tarski])).
% 36.56/36.80  thf(d4_relat_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 36.56/36.80       ( ![C:$i]:
% 36.56/36.80         ( ( r2_hidden @ C @ B ) <=>
% 36.56/36.80           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 36.56/36.80  thf('14', plain,
% 36.56/36.80      (![X51 : $i, X52 : $i, X53 : $i]:
% 36.56/36.80         (~ (r2_hidden @ X53 @ X52)
% 36.56/36.80          | (r2_hidden @ (k4_tarski @ X53 @ (sk_D_1 @ X53 @ X51)) @ X51)
% 36.56/36.80          | ((X52) != (k1_relat_1 @ X51)))),
% 36.56/36.80      inference('cnf', [status(esa)], [d4_relat_1])).
% 36.56/36.80  thf('15', plain,
% 36.56/36.80      (![X51 : $i, X53 : $i]:
% 36.56/36.80         ((r2_hidden @ (k4_tarski @ X53 @ (sk_D_1 @ X53 @ X51)) @ X51)
% 36.56/36.80          | ~ (r2_hidden @ X53 @ (k1_relat_1 @ X51)))),
% 36.56/36.80      inference('simplify', [status(thm)], ['14'])).
% 36.56/36.80  thf('16', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 36.56/36.80          | (r2_hidden @ 
% 36.56/36.80             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 36.56/36.80              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 36.56/36.80             X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['13', '15'])).
% 36.56/36.80  thf(t48_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 36.56/36.80  thf('17', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 36.56/36.80  thf('18', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 36.56/36.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.56/36.80  thf('19', plain,
% 36.56/36.80      (![X13 : $i, X15 : $i]:
% 36.56/36.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.56/36.80          | ~ (r1_tarski @ X13 @ X15))),
% 36.56/36.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.56/36.80  thf('20', plain,
% 36.56/36.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['18', '19'])).
% 36.56/36.80  thf('21', plain,
% 36.56/36.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['17', '20'])).
% 36.56/36.80  thf(t4_xboole_0, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 36.56/36.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 36.56/36.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 36.56/36.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 36.56/36.80  thf('22', plain,
% 36.56/36.80      (![X6 : $i, X8 : $i, X9 : $i]:
% 36.56/36.80         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 36.56/36.80          | ~ (r1_xboole_0 @ X6 @ X9))),
% 36.56/36.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 36.56/36.80  thf('23', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['21', '22'])).
% 36.56/36.80  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 36.56/36.80  thf('24', plain, (![X34 : $i]: (r1_xboole_0 @ X34 @ k1_xboole_0)),
% 36.56/36.80      inference('cnf', [status(esa)], [t65_xboole_1])).
% 36.56/36.80  thf(symmetry_r1_xboole_0, axiom,
% 36.56/36.80    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 36.56/36.80  thf('25', plain,
% 36.56/36.80      (![X4 : $i, X5 : $i]:
% 36.56/36.80         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 36.56/36.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 36.56/36.80  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 36.56/36.80      inference('sup-', [status(thm)], ['24', '25'])).
% 36.56/36.80  thf('27', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 36.56/36.80      inference('demod', [status(thm)], ['23', '26'])).
% 36.56/36.80  thf('28', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 36.56/36.80      inference('sup-', [status(thm)], ['16', '27'])).
% 36.56/36.80  thf('29', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 36.56/36.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.56/36.80  thf(d10_xboole_0, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.56/36.80  thf('30', plain,
% 36.56/36.80      (![X10 : $i, X12 : $i]:
% 36.56/36.80         (((X10) = (X12))
% 36.56/36.80          | ~ (r1_tarski @ X12 @ X10)
% 36.56/36.80          | ~ (r1_tarski @ X10 @ X12))),
% 36.56/36.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.56/36.80  thf('31', plain,
% 36.56/36.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['29', '30'])).
% 36.56/36.80  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['28', '31'])).
% 36.56/36.80  thf(d6_relat_1, axiom,
% 36.56/36.80    (![A:$i]:
% 36.56/36.80     ( ( v1_relat_1 @ A ) =>
% 36.56/36.80       ( ( k3_relat_1 @ A ) =
% 36.56/36.80         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 36.56/36.80  thf('33', plain,
% 36.56/36.80      (![X56 : $i]:
% 36.56/36.80         (((k3_relat_1 @ X56)
% 36.56/36.80            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 36.56/36.80          | ~ (v1_relat_1 @ X56))),
% 36.56/36.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 36.56/36.80  thf('34', plain,
% 36.56/36.80      ((((k3_relat_1 @ k1_xboole_0)
% 36.56/36.80          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 36.56/36.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['32', '33'])).
% 36.56/36.80  thf(commutativity_k2_tarski, axiom,
% 36.56/36.80    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 36.56/36.80  thf('35', plain,
% 36.56/36.80      (![X38 : $i, X39 : $i]:
% 36.56/36.80         ((k2_tarski @ X39 @ X38) = (k2_tarski @ X38 @ X39))),
% 36.56/36.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 36.56/36.80  thf(l51_zfmisc_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 36.56/36.80  thf('36', plain,
% 36.56/36.80      (![X42 : $i, X43 : $i]:
% 36.56/36.80         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 36.56/36.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 36.56/36.80  thf('37', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['35', '36'])).
% 36.56/36.80  thf('38', plain,
% 36.56/36.80      (![X42 : $i, X43 : $i]:
% 36.56/36.80         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 36.56/36.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 36.56/36.80  thf('39', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['37', '38'])).
% 36.56/36.80  thf('40', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 36.56/36.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.56/36.80  thf('41', plain,
% 36.56/36.80      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 36.56/36.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.56/36.80  thf('42', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 36.56/36.80      inference('simplify', [status(thm)], ['41'])).
% 36.56/36.80  thf(t8_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i,C:$i]:
% 36.56/36.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 36.56/36.80       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 36.56/36.80  thf('43', plain,
% 36.56/36.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 36.56/36.80         (~ (r1_tarski @ X35 @ X36)
% 36.56/36.80          | ~ (r1_tarski @ X37 @ X36)
% 36.56/36.80          | (r1_tarski @ (k2_xboole_0 @ X35 @ X37) @ X36))),
% 36.56/36.80      inference('cnf', [status(esa)], [t8_xboole_1])).
% 36.56/36.80  thf('44', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['42', '43'])).
% 36.56/36.80  thf('45', plain,
% 36.56/36.80      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 36.56/36.80      inference('sup-', [status(thm)], ['40', '44'])).
% 36.56/36.80  thf('46', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 36.56/36.80      inference('simplify', [status(thm)], ['41'])).
% 36.56/36.80  thf(t11_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i,C:$i]:
% 36.56/36.80     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 36.56/36.80  thf('47', plain,
% 36.56/36.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.56/36.80         ((r1_tarski @ X19 @ X20)
% 36.56/36.80          | ~ (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ X20))),
% 36.56/36.80      inference('cnf', [status(esa)], [t11_xboole_1])).
% 36.56/36.80  thf('48', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['46', '47'])).
% 36.56/36.80  thf('49', plain,
% 36.56/36.80      (![X10 : $i, X12 : $i]:
% 36.56/36.80         (((X10) = (X12))
% 36.56/36.80          | ~ (r1_tarski @ X12 @ X10)
% 36.56/36.80          | ~ (r1_tarski @ X10 @ X12))),
% 36.56/36.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.56/36.80  thf('50', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.56/36.80          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['48', '49'])).
% 36.56/36.80  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['45', '50'])).
% 36.56/36.80  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['39', '51'])).
% 36.56/36.80  thf('53', plain,
% 36.56/36.80      ((((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 36.56/36.80        | ~ (v1_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('demod', [status(thm)], ['34', '52'])).
% 36.56/36.80  thf('54', plain,
% 36.56/36.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 36.56/36.80        | ((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['12', '53'])).
% 36.56/36.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 36.56/36.80  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 36.56/36.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 36.56/36.80  thf('56', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('demod', [status(thm)], ['54', '55'])).
% 36.56/36.80  thf('57', plain,
% 36.56/36.80      ((r1_tarski @ 
% 36.56/36.80        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 36.56/36.80        (k3_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('demod', [status(thm)], ['11', '56'])).
% 36.56/36.80  thf('58', plain, (![X48 : $i]: ((v1_relat_1 @ X48) | ~ (v1_xboole_0 @ X48))),
% 36.56/36.80      inference('cnf', [status(esa)], [cc1_relat_1])).
% 36.56/36.80  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['28', '31'])).
% 36.56/36.80  thf('60', plain,
% 36.56/36.80      (![X1 : $i, X3 : $i]:
% 36.56/36.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 36.56/36.80      inference('cnf', [status(esa)], [d3_tarski])).
% 36.56/36.80  thf(t19_relat_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( v1_relat_1 @ B ) =>
% 36.56/36.80       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 36.56/36.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 36.56/36.80  thf('61', plain,
% 36.56/36.80      (![X59 : $i, X60 : $i]:
% 36.56/36.80         ((r2_hidden @ (sk_C_3 @ X59) @ (k1_relat_1 @ X59))
% 36.56/36.80          | ~ (r2_hidden @ X60 @ (k2_relat_1 @ X59))
% 36.56/36.80          | ~ (v1_relat_1 @ X59))),
% 36.56/36.80      inference('cnf', [status(esa)], [t19_relat_1])).
% 36.56/36.80  thf('62', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 36.56/36.80          | ~ (v1_relat_1 @ X0)
% 36.56/36.80          | (r2_hidden @ (sk_C_3 @ X0) @ (k1_relat_1 @ X0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['60', '61'])).
% 36.56/36.80  thf('63', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 36.56/36.80      inference('simplify', [status(thm)], ['41'])).
% 36.56/36.80  thf('64', plain,
% 36.56/36.80      (![X13 : $i, X15 : $i]:
% 36.56/36.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.56/36.80          | ~ (r1_tarski @ X13 @ X15))),
% 36.56/36.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.56/36.80  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['63', '64'])).
% 36.56/36.80  thf('66', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf('67', plain,
% 36.56/36.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['65', '66'])).
% 36.56/36.80  thf(t3_boole, axiom,
% 36.56/36.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 36.56/36.80  thf('68', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 36.56/36.80      inference('cnf', [status(esa)], [t3_boole])).
% 36.56/36.80  thf('69', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 36.56/36.80      inference('demod', [status(thm)], ['67', '68'])).
% 36.56/36.80  thf('70', plain,
% 36.56/36.80      (![X6 : $i, X8 : $i, X9 : $i]:
% 36.56/36.80         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 36.56/36.80          | ~ (r1_xboole_0 @ X6 @ X9))),
% 36.56/36.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 36.56/36.80  thf('71', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['69', '70'])).
% 36.56/36.80  thf('72', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X0)
% 36.56/36.80          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 36.56/36.80          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['62', '71'])).
% 36.56/36.80  thf('73', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         (~ (r1_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 36.56/36.80          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 36.56/36.80          | ~ (v1_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['59', '72'])).
% 36.56/36.80  thf('74', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['28', '31'])).
% 36.56/36.80  thf('75', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 36.56/36.80      inference('sup-', [status(thm)], ['24', '25'])).
% 36.56/36.80  thf('76', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('demod', [status(thm)], ['54', '55'])).
% 36.56/36.80  thf('77', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         ((r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ X0)
% 36.56/36.80          | ~ (v1_relat_1 @ k1_xboole_0))),
% 36.56/36.80      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 36.56/36.80  thf('78', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         (~ (v1_xboole_0 @ k1_xboole_0)
% 36.56/36.80          | (r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['58', '77'])).
% 36.56/36.80  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 36.56/36.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 36.56/36.80  thf('80', plain, (![X0 : $i]: (r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ X0)),
% 36.56/36.80      inference('demod', [status(thm)], ['78', '79'])).
% 36.56/36.80  thf('81', plain,
% 36.56/36.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['29', '30'])).
% 36.56/36.80  thf('82', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['80', '81'])).
% 36.56/36.80  thf('83', plain,
% 36.56/36.80      ((r1_tarski @ 
% 36.56/36.80        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ k1_xboole_0)),
% 36.56/36.80      inference('demod', [status(thm)], ['57', '82'])).
% 36.56/36.80  thf('84', plain,
% 36.56/36.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['29', '30'])).
% 36.56/36.80  thf('85', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 36.56/36.80         = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['83', '84'])).
% 36.56/36.80  thf('86', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf('87', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ k1_xboole_0)
% 36.56/36.80         = (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 36.56/36.80      inference('sup+', [status(thm)], ['85', '86'])).
% 36.56/36.80  thf('88', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 36.56/36.80      inference('cnf', [status(esa)], [t3_boole])).
% 36.56/36.80  thf('89', plain,
% 36.56/36.80      (((k2_relat_1 @ sk_A)
% 36.56/36.80         = (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 36.56/36.80      inference('demod', [status(thm)], ['87', '88'])).
% 36.56/36.80  thf('90', plain,
% 36.56/36.80      (![X56 : $i]:
% 36.56/36.80         (((k3_relat_1 @ X56)
% 36.56/36.80            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 36.56/36.80          | ~ (v1_relat_1 @ X56))),
% 36.56/36.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 36.56/36.80  thf('91', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['46', '47'])).
% 36.56/36.80  thf('92', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 36.56/36.80          | ~ (v1_relat_1 @ X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['90', '91'])).
% 36.56/36.80  thf('93', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['1', '2'])).
% 36.56/36.80  thf(t15_relat_1, axiom,
% 36.56/36.80    (![A:$i]:
% 36.56/36.80     ( ( v1_relat_1 @ A ) =>
% 36.56/36.80       ( ![B:$i]:
% 36.56/36.80         ( ( v1_relat_1 @ B ) =>
% 36.56/36.80           ( r1_tarski @
% 36.56/36.80             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 36.56/36.80             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 36.56/36.80  thf('94', plain,
% 36.56/36.80      (![X57 : $i, X58 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X57)
% 36.56/36.80          | (r1_tarski @ 
% 36.56/36.80             (k6_subset_1 @ (k1_relat_1 @ X58) @ (k1_relat_1 @ X57)) @ 
% 36.56/36.80             (k1_relat_1 @ (k6_subset_1 @ X58 @ X57)))
% 36.56/36.80          | ~ (v1_relat_1 @ X58))),
% 36.56/36.80      inference('cnf', [status(esa)], [t15_relat_1])).
% 36.56/36.80  thf('95', plain,
% 36.56/36.80      (![X44 : $i, X45 : $i]:
% 36.56/36.80         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 36.56/36.80      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 36.56/36.80  thf('96', plain,
% 36.56/36.80      (![X44 : $i, X45 : $i]:
% 36.56/36.80         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 36.56/36.80      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 36.56/36.80  thf('97', plain,
% 36.56/36.80      (![X57 : $i, X58 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X57)
% 36.56/36.80          | (r1_tarski @ 
% 36.56/36.80             (k4_xboole_0 @ (k1_relat_1 @ X58) @ (k1_relat_1 @ X57)) @ 
% 36.56/36.80             (k1_relat_1 @ (k4_xboole_0 @ X58 @ X57)))
% 36.56/36.80          | ~ (v1_relat_1 @ X58))),
% 36.56/36.80      inference('demod', [status(thm)], ['94', '95', '96'])).
% 36.56/36.80  thf('98', plain,
% 36.56/36.80      (![X10 : $i, X12 : $i]:
% 36.56/36.80         (((X10) = (X12))
% 36.56/36.80          | ~ (r1_tarski @ X12 @ X10)
% 36.56/36.80          | ~ (r1_tarski @ X10 @ X12))),
% 36.56/36.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.56/36.80  thf('99', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X1)
% 36.56/36.80          | ~ (v1_relat_1 @ X0)
% 36.56/36.80          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 36.56/36.80               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 36.56/36.80          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 36.56/36.80              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 36.56/36.80      inference('sup-', [status(thm)], ['97', '98'])).
% 36.56/36.80  thf('100', plain,
% 36.56/36.80      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 36.56/36.80           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 36.56/36.80        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B))
% 36.56/36.80            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 36.56/36.80        | ~ (v1_relat_1 @ sk_B)
% 36.56/36.80        | ~ (v1_relat_1 @ sk_A))),
% 36.56/36.80      inference('sup-', [status(thm)], ['93', '99'])).
% 36.56/36.80  thf('101', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['28', '31'])).
% 36.56/36.80  thf('102', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 36.56/36.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.56/36.80  thf('103', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['1', '2'])).
% 36.56/36.80  thf('104', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['28', '31'])).
% 36.56/36.80  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('107', plain,
% 36.56/36.80      (((k1_xboole_0)
% 36.56/36.80         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 36.56/36.80      inference('demod', [status(thm)],
% 36.56/36.80                ['100', '101', '102', '103', '104', '105', '106'])).
% 36.56/36.80  thf('108', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf('109', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)
% 36.56/36.80         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 36.56/36.80      inference('sup+', [status(thm)], ['107', '108'])).
% 36.56/36.80  thf('110', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 36.56/36.80      inference('cnf', [status(esa)], [t3_boole])).
% 36.56/36.80  thf('111', plain,
% 36.56/36.80      (((k1_relat_1 @ sk_A)
% 36.56/36.80         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 36.56/36.80      inference('demod', [status(thm)], ['109', '110'])).
% 36.56/36.80  thf('112', plain,
% 36.56/36.80      (![X38 : $i, X39 : $i]:
% 36.56/36.80         ((k2_tarski @ X39 @ X38) = (k2_tarski @ X38 @ X39))),
% 36.56/36.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 36.56/36.80  thf(t12_setfam_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]:
% 36.56/36.80     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 36.56/36.80  thf('113', plain,
% 36.56/36.80      (![X46 : $i, X47 : $i]:
% 36.56/36.80         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 36.56/36.80      inference('cnf', [status(esa)], [t12_setfam_1])).
% 36.56/36.80  thf('114', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['112', '113'])).
% 36.56/36.80  thf('115', plain,
% 36.56/36.80      (![X46 : $i, X47 : $i]:
% 36.56/36.80         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 36.56/36.80      inference('cnf', [status(esa)], [t12_setfam_1])).
% 36.56/36.80  thf('116', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['114', '115'])).
% 36.56/36.80  thf('117', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf(t36_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 36.56/36.80  thf('118', plain,
% 36.56/36.80      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 36.56/36.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 36.56/36.80  thf('119', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 36.56/36.80      inference('sup+', [status(thm)], ['117', '118'])).
% 36.56/36.80  thf('120', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['42', '43'])).
% 36.56/36.80  thf('121', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (r1_tarski @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 36.56/36.80      inference('sup-', [status(thm)], ['119', '120'])).
% 36.56/36.80  thf('122', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.56/36.80          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['48', '49'])).
% 36.56/36.80  thf('123', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['121', '122'])).
% 36.56/36.80  thf('124', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['116', '123'])).
% 36.56/36.80  thf('125', plain,
% 36.56/36.80      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 36.56/36.80         = (k1_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup+', [status(thm)], ['111', '124'])).
% 36.56/36.80  thf('126', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['37', '38'])).
% 36.56/36.80  thf('127', plain,
% 36.56/36.80      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 36.56/36.80         = (k1_relat_1 @ sk_B))),
% 36.56/36.80      inference('demod', [status(thm)], ['125', '126'])).
% 36.56/36.80  thf('128', plain,
% 36.56/36.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.56/36.80         ((r1_tarski @ X19 @ X20)
% 36.56/36.80          | ~ (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ X20))),
% 36.56/36.80      inference('cnf', [status(esa)], [t11_xboole_1])).
% 36.56/36.80  thf('129', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 36.56/36.80          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['127', '128'])).
% 36.56/36.80  thf('130', plain,
% 36.56/36.80      ((~ (v1_relat_1 @ sk_B)
% 36.56/36.80        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['92', '129'])).
% 36.56/36.80  thf('131', plain, ((v1_relat_1 @ sk_B)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('132', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('demod', [status(thm)], ['130', '131'])).
% 36.56/36.80  thf('133', plain,
% 36.56/36.80      (![X13 : $i, X15 : $i]:
% 36.56/36.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.56/36.80          | ~ (r1_tarski @ X13 @ X15))),
% 36.56/36.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.56/36.80  thf('134', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 36.56/36.80         = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['132', '133'])).
% 36.56/36.80  thf('135', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf('136', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)
% 36.56/36.80         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 36.56/36.80      inference('sup+', [status(thm)], ['134', '135'])).
% 36.56/36.80  thf('137', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 36.56/36.80      inference('cnf', [status(esa)], [t3_boole])).
% 36.56/36.80  thf('138', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['114', '115'])).
% 36.56/36.80  thf('139', plain,
% 36.56/36.80      (((k1_relat_1 @ sk_A)
% 36.56/36.80         = (k3_xboole_0 @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 36.56/36.80      inference('demod', [status(thm)], ['136', '137', '138'])).
% 36.56/36.80  thf('140', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['121', '122'])).
% 36.56/36.80  thf('141', plain,
% 36.56/36.80      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 36.56/36.80         = (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup+', [status(thm)], ['139', '140'])).
% 36.56/36.80  thf('142', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['46', '47'])).
% 36.56/36.80  thf('143', plain,
% 36.56/36.80      (![X56 : $i]:
% 36.56/36.80         (((k3_relat_1 @ X56)
% 36.56/36.80            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 36.56/36.80          | ~ (v1_relat_1 @ X56))),
% 36.56/36.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 36.56/36.80  thf('144', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['37', '38'])).
% 36.56/36.80  thf('145', plain,
% 36.56/36.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.56/36.80         ((r1_tarski @ X19 @ X20)
% 36.56/36.80          | ~ (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ X20))),
% 36.56/36.80      inference('cnf', [status(esa)], [t11_xboole_1])).
% 36.56/36.80  thf('146', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.56/36.80         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 36.56/36.80      inference('sup-', [status(thm)], ['144', '145'])).
% 36.56/36.80  thf('147', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 36.56/36.80          | ~ (v1_relat_1 @ X0)
% 36.56/36.80          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 36.56/36.80      inference('sup-', [status(thm)], ['143', '146'])).
% 36.56/36.80  thf('148', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 36.56/36.80           (k2_xboole_0 @ (k3_relat_1 @ X1) @ X0))
% 36.56/36.80          | ~ (v1_relat_1 @ X1))),
% 36.56/36.80      inference('sup-', [status(thm)], ['142', '147'])).
% 36.56/36.80  thf('149', plain,
% 36.56/36.80      (((r1_tarski @ (k2_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))
% 36.56/36.80        | ~ (v1_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup+', [status(thm)], ['141', '148'])).
% 36.56/36.80  thf('150', plain, ((v1_relat_1 @ sk_B)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('151', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('demod', [status(thm)], ['149', '150'])).
% 36.56/36.80  thf('152', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['116', '123'])).
% 36.56/36.80  thf('153', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.56/36.80         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 36.56/36.80      inference('sup-', [status(thm)], ['144', '145'])).
% 36.56/36.80  thf('154', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.56/36.80         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 36.56/36.80      inference('sup-', [status(thm)], ['152', '153'])).
% 36.56/36.80  thf('155', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 36.56/36.80          (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup-', [status(thm)], ['151', '154'])).
% 36.56/36.80  thf('156', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup+', [status(thm)], ['89', '155'])).
% 36.56/36.80  thf('157', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('demod', [status(thm)], ['130', '131'])).
% 36.56/36.80  thf('158', plain,
% 36.56/36.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 36.56/36.80         (~ (r1_tarski @ X35 @ X36)
% 36.56/36.80          | ~ (r1_tarski @ X37 @ X36)
% 36.56/36.80          | (r1_tarski @ (k2_xboole_0 @ X35 @ X37) @ X36))),
% 36.56/36.80      inference('cnf', [status(esa)], [t8_xboole_1])).
% 36.56/36.80  thf('159', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 36.56/36.80           (k3_relat_1 @ sk_B))
% 36.56/36.80          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['157', '158'])).
% 36.56/36.80  thf('160', plain,
% 36.56/36.80      ((r1_tarski @ 
% 36.56/36.80        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 36.56/36.80        (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('sup-', [status(thm)], ['156', '159'])).
% 36.56/36.80  thf('161', plain,
% 36.56/36.80      (((k1_relat_1 @ sk_A)
% 36.56/36.80         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 36.56/36.80      inference('demod', [status(thm)], ['109', '110'])).
% 36.56/36.80  thf('162', plain,
% 36.56/36.80      (![X56 : $i]:
% 36.56/36.80         (((k3_relat_1 @ X56)
% 36.56/36.80            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 36.56/36.80          | ~ (v1_relat_1 @ X56))),
% 36.56/36.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 36.56/36.80  thf('163', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf('164', plain,
% 36.56/36.80      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 36.56/36.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 36.56/36.80  thf('165', plain,
% 36.56/36.80      (![X13 : $i, X15 : $i]:
% 36.56/36.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.56/36.80          | ~ (r1_tarski @ X13 @ X15))),
% 36.56/36.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.56/36.80  thf('166', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['164', '165'])).
% 36.56/36.80  thf('167', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['163', '166'])).
% 36.56/36.80  thf(t44_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i,C:$i]:
% 36.56/36.80     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 36.56/36.80       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 36.56/36.80  thf('168', plain,
% 36.56/36.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 36.56/36.80         ((r1_tarski @ X29 @ (k2_xboole_0 @ X30 @ X31))
% 36.56/36.80          | ~ (r1_tarski @ (k4_xboole_0 @ X29 @ X30) @ X31))),
% 36.56/36.80      inference('cnf', [status(esa)], [t44_xboole_1])).
% 36.56/36.80  thf('169', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.56/36.80         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 36.56/36.80          | (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['167', '168'])).
% 36.56/36.80  thf('170', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 36.56/36.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.56/36.80  thf('171', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.56/36.80         (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('demod', [status(thm)], ['169', '170'])).
% 36.56/36.80  thf('172', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 36.56/36.80           (k3_relat_1 @ X0))
% 36.56/36.80          | ~ (v1_relat_1 @ X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['162', '171'])).
% 36.56/36.80  thf('173', plain,
% 36.56/36.80      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))
% 36.56/36.80        | ~ (v1_relat_1 @ sk_A))),
% 36.56/36.80      inference('sup+', [status(thm)], ['161', '172'])).
% 36.56/36.80  thf('174', plain, ((v1_relat_1 @ sk_A)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('175', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 36.56/36.80      inference('demod', [status(thm)], ['173', '174'])).
% 36.56/36.80  thf('176', plain,
% 36.56/36.80      (![X13 : $i, X15 : $i]:
% 36.56/36.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.56/36.80          | ~ (r1_tarski @ X13 @ X15))),
% 36.56/36.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.56/36.80  thf('177', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))
% 36.56/36.80         = (k1_xboole_0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['175', '176'])).
% 36.56/36.80  thf('178', plain,
% 36.56/36.80      (![X32 : $i, X33 : $i]:
% 36.56/36.80         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 36.56/36.80           = (k3_xboole_0 @ X32 @ X33))),
% 36.56/36.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 36.56/36.80  thf('179', plain,
% 36.56/36.80      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)
% 36.56/36.80         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A)))),
% 36.56/36.80      inference('sup+', [status(thm)], ['177', '178'])).
% 36.56/36.80  thf('180', plain, (![X25 : $i]: ((k4_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 36.56/36.80      inference('cnf', [status(esa)], [t3_boole])).
% 36.56/36.80  thf('181', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['114', '115'])).
% 36.56/36.80  thf('182', plain,
% 36.56/36.80      (((k1_relat_1 @ sk_A)
% 36.56/36.80         = (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)))),
% 36.56/36.80      inference('demod', [status(thm)], ['179', '180', '181'])).
% 36.56/36.80  thf('183', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['121', '122'])).
% 36.56/36.80  thf('184', plain,
% 36.56/36.80      (((k2_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 36.56/36.80         = (k3_relat_1 @ sk_A))),
% 36.56/36.80      inference('sup+', [status(thm)], ['182', '183'])).
% 36.56/36.80  thf('185', plain,
% 36.56/36.80      (![X56 : $i]:
% 36.56/36.80         (((k3_relat_1 @ X56)
% 36.56/36.80            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 36.56/36.80          | ~ (v1_relat_1 @ X56))),
% 36.56/36.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 36.56/36.80  thf('186', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['46', '47'])).
% 36.56/36.80  thf('187', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['42', '43'])).
% 36.56/36.80  thf('188', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 36.56/36.80          (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['186', '187'])).
% 36.56/36.80  thf('189', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['37', '38'])).
% 36.56/36.80  thf('190', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (r1_tarski @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 36.56/36.80          (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('demod', [status(thm)], ['188', '189'])).
% 36.56/36.80  thf('191', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0)) @ 
% 36.56/36.80           (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 36.56/36.80          | ~ (v1_relat_1 @ X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['185', '190'])).
% 36.56/36.80  thf('192', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['37', '38'])).
% 36.56/36.80  thf('193', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 36.56/36.80           (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 36.56/36.80          | ~ (v1_relat_1 @ X0))),
% 36.56/36.80      inference('demod', [status(thm)], ['191', '192'])).
% 36.56/36.80  thf('194', plain,
% 36.56/36.80      (((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 36.56/36.80         (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 36.56/36.80        | ~ (v1_relat_1 @ sk_A))),
% 36.56/36.80      inference('sup+', [status(thm)], ['184', '193'])).
% 36.56/36.80  thf('195', plain, ((v1_relat_1 @ sk_A)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('196', plain,
% 36.56/36.80      ((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 36.56/36.80        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 36.56/36.80      inference('demod', [status(thm)], ['194', '195'])).
% 36.56/36.80  thf('197', plain,
% 36.56/36.80      (![X10 : $i, X12 : $i]:
% 36.56/36.80         (((X10) = (X12))
% 36.56/36.80          | ~ (r1_tarski @ X12 @ X10)
% 36.56/36.80          | ~ (r1_tarski @ X10 @ X12))),
% 36.56/36.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.56/36.80  thf('198', plain,
% 36.56/36.80      ((~ (r1_tarski @ 
% 36.56/36.80           (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 36.56/36.80           (k3_relat_1 @ sk_A))
% 36.56/36.80        | ((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 36.56/36.80            = (k3_relat_1 @ sk_A)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['196', '197'])).
% 36.56/36.80  thf('199', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 36.56/36.80      inference('demod', [status(thm)], ['173', '174'])).
% 36.56/36.80  thf('200', plain,
% 36.56/36.80      (![X56 : $i]:
% 36.56/36.80         (((k3_relat_1 @ X56)
% 36.56/36.80            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 36.56/36.80          | ~ (v1_relat_1 @ X56))),
% 36.56/36.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 36.56/36.80  thf('201', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 36.56/36.80      inference('simplify', [status(thm)], ['41'])).
% 36.56/36.80  thf(t10_xboole_1, axiom,
% 36.56/36.80    (![A:$i,B:$i,C:$i]:
% 36.56/36.80     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 36.56/36.80  thf('202', plain,
% 36.56/36.80      (![X16 : $i, X17 : $i, X18 : $i]:
% 36.56/36.80         (~ (r1_tarski @ X16 @ X17)
% 36.56/36.80          | (r1_tarski @ X16 @ (k2_xboole_0 @ X18 @ X17)))),
% 36.56/36.80      inference('cnf', [status(esa)], [t10_xboole_1])).
% 36.56/36.80  thf('203', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 36.56/36.80      inference('sup-', [status(thm)], ['201', '202'])).
% 36.56/36.80  thf('204', plain,
% 36.56/36.80      (![X0 : $i]:
% 36.56/36.80         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 36.56/36.80          | ~ (v1_relat_1 @ X0))),
% 36.56/36.80      inference('sup+', [status(thm)], ['200', '203'])).
% 36.56/36.80  thf('205', plain,
% 36.56/36.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 36.56/36.80         (~ (r1_tarski @ X35 @ X36)
% 36.56/36.80          | ~ (r1_tarski @ X37 @ X36)
% 36.56/36.80          | (r1_tarski @ (k2_xboole_0 @ X35 @ X37) @ X36))),
% 36.56/36.80      inference('cnf', [status(esa)], [t8_xboole_1])).
% 36.56/36.80  thf('206', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]:
% 36.56/36.80         (~ (v1_relat_1 @ X0)
% 36.56/36.80          | (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ 
% 36.56/36.80             (k3_relat_1 @ X0))
% 36.56/36.80          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 36.56/36.80      inference('sup-', [status(thm)], ['204', '205'])).
% 36.56/36.80  thf('207', plain,
% 36.56/36.80      (((r1_tarski @ 
% 36.56/36.80         (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 36.56/36.80         (k3_relat_1 @ sk_A))
% 36.56/36.80        | ~ (v1_relat_1 @ sk_A))),
% 36.56/36.80      inference('sup-', [status(thm)], ['199', '206'])).
% 36.56/36.80  thf('208', plain,
% 36.56/36.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 36.56/36.80      inference('sup+', [status(thm)], ['37', '38'])).
% 36.56/36.80  thf('209', plain, ((v1_relat_1 @ sk_A)),
% 36.56/36.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.56/36.80  thf('210', plain,
% 36.56/36.80      ((r1_tarski @ 
% 36.56/36.80        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 36.56/36.80        (k3_relat_1 @ sk_A))),
% 36.56/36.80      inference('demod', [status(thm)], ['207', '208', '209'])).
% 36.56/36.80  thf('211', plain,
% 36.56/36.80      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 36.56/36.80         = (k3_relat_1 @ sk_A))),
% 36.56/36.80      inference('demod', [status(thm)], ['198', '210'])).
% 36.56/36.80  thf('212', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 36.56/36.80      inference('demod', [status(thm)], ['160', '211'])).
% 36.56/36.80  thf('213', plain, ($false), inference('demod', [status(thm)], ['0', '212'])).
% 36.56/36.80  
% 36.56/36.80  % SZS output end Refutation
% 36.56/36.80  
% 36.56/36.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
