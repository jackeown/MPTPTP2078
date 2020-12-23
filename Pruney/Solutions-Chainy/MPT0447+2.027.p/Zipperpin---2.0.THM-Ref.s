%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mTKxcZDiM8

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:56 EST 2020

% Result     : Theorem 4.18s
% Output     : Refutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 456 expanded)
%              Number of leaves         :   40 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  979 (3272 expanded)
%              Number of equality atoms :   42 ( 158 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X49: $i] :
      ( ( ( k3_relat_1 @ X49 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X49: $i] :
      ( ( ( k3_relat_1 @ X49 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X49 ) @ ( k1_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X49: $i] :
      ( ( ( k3_relat_1 @ X49 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X49 ) @ ( k1_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X51 ) @ ( k1_relat_1 @ X50 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X51 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X51 ) @ ( k1_relat_1 @ X50 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X51 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('32',plain,(
    ! [X44: $i,X47: $i] :
      ( ( X47
        = ( k1_relat_1 @ X44 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X47 @ X44 ) @ ( sk_D @ X47 @ X44 ) ) @ X44 )
      | ( r2_hidden @ ( sk_C_1 @ X47 @ X44 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('33',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('38',plain,(
    ! [X28: $i] :
      ( r1_xboole_0 @ X28 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('48',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','44','45','46','47','48','49'])).

thf('51',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('59',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('63',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('71',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X49: $i] :
      ( ( ( k3_relat_1 @ X49 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X49 ) @ ( k1_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('83',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('88',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['86','89'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X53 @ X52 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X53 ) @ ( k2_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','97'])).

thf('99',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('100',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('104',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mTKxcZDiM8
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:37:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.18/4.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.18/4.37  % Solved by: fo/fo7.sh
% 4.18/4.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.18/4.37  % done 7582 iterations in 3.919s
% 4.18/4.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.18/4.37  % SZS output start Refutation
% 4.18/4.37  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 4.18/4.37  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.18/4.37  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.18/4.37  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.18/4.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.18/4.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.18/4.37  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.18/4.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.18/4.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.18/4.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.18/4.37  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 4.18/4.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.18/4.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.18/4.37  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.18/4.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.18/4.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.18/4.37  thf(sk_A_type, type, sk_A: $i).
% 4.18/4.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.18/4.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.18/4.37  thf(t31_relat_1, conjecture,
% 4.18/4.37    (![A:$i]:
% 4.18/4.37     ( ( v1_relat_1 @ A ) =>
% 4.18/4.37       ( ![B:$i]:
% 4.18/4.37         ( ( v1_relat_1 @ B ) =>
% 4.18/4.37           ( ( r1_tarski @ A @ B ) =>
% 4.18/4.37             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 4.18/4.37  thf(zf_stmt_0, negated_conjecture,
% 4.18/4.37    (~( ![A:$i]:
% 4.18/4.37        ( ( v1_relat_1 @ A ) =>
% 4.18/4.37          ( ![B:$i]:
% 4.18/4.37            ( ( v1_relat_1 @ B ) =>
% 4.18/4.37              ( ( r1_tarski @ A @ B ) =>
% 4.18/4.37                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 4.18/4.37    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 4.18/4.37  thf('0', plain,
% 4.18/4.37      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf(d6_relat_1, axiom,
% 4.18/4.37    (![A:$i]:
% 4.18/4.37     ( ( v1_relat_1 @ A ) =>
% 4.18/4.37       ( ( k3_relat_1 @ A ) =
% 4.18/4.37         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 4.18/4.37  thf('1', plain,
% 4.18/4.37      (![X49 : $i]:
% 4.18/4.37         (((k3_relat_1 @ X49)
% 4.18/4.37            = (k2_xboole_0 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49)))
% 4.18/4.37          | ~ (v1_relat_1 @ X49))),
% 4.18/4.37      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.18/4.37  thf(commutativity_k2_tarski, axiom,
% 4.18/4.37    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.18/4.37  thf('2', plain,
% 4.18/4.37      (![X34 : $i, X35 : $i]:
% 4.18/4.37         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 4.18/4.37      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.18/4.37  thf(l51_zfmisc_1, axiom,
% 4.18/4.37    (![A:$i,B:$i]:
% 4.18/4.37     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.18/4.37  thf('3', plain,
% 4.18/4.37      (![X36 : $i, X37 : $i]:
% 4.18/4.37         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 4.18/4.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.18/4.37  thf('4', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.18/4.37      inference('sup+', [status(thm)], ['2', '3'])).
% 4.18/4.37  thf('5', plain,
% 4.18/4.37      (![X36 : $i, X37 : $i]:
% 4.18/4.37         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 4.18/4.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.18/4.37  thf('6', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.18/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.18/4.37  thf('7', plain,
% 4.18/4.37      (![X49 : $i]:
% 4.18/4.37         (((k3_relat_1 @ X49)
% 4.18/4.37            = (k2_xboole_0 @ (k2_relat_1 @ X49) @ (k1_relat_1 @ X49)))
% 4.18/4.37          | ~ (v1_relat_1 @ X49))),
% 4.18/4.37      inference('demod', [status(thm)], ['1', '6'])).
% 4.18/4.37  thf('8', plain,
% 4.18/4.37      (![X49 : $i]:
% 4.18/4.37         (((k3_relat_1 @ X49)
% 4.18/4.37            = (k2_xboole_0 @ (k2_relat_1 @ X49) @ (k1_relat_1 @ X49)))
% 4.18/4.37          | ~ (v1_relat_1 @ X49))),
% 4.18/4.37      inference('demod', [status(thm)], ['1', '6'])).
% 4.18/4.37  thf(d10_xboole_0, axiom,
% 4.18/4.37    (![A:$i,B:$i]:
% 4.18/4.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.18/4.37  thf('9', plain,
% 4.18/4.37      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 4.18/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.18/4.37  thf('10', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.18/4.37      inference('simplify', [status(thm)], ['9'])).
% 4.18/4.37  thf(t10_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i,C:$i]:
% 4.18/4.37     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 4.18/4.37  thf('11', plain,
% 4.18/4.37      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X10 @ X11)
% 4.18/4.37          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 4.18/4.37      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.18/4.37  thf('12', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['10', '11'])).
% 4.18/4.37  thf('13', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 4.18/4.37          | ~ (v1_relat_1 @ X0))),
% 4.18/4.37      inference('sup+', [status(thm)], ['8', '12'])).
% 4.18/4.37  thf(t7_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.18/4.37  thf('14', plain,
% 4.18/4.37      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 4.18/4.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.18/4.37  thf('15', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf(t1_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i,C:$i]:
% 4.18/4.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.18/4.37       ( r1_tarski @ A @ C ) ))).
% 4.18/4.37  thf('16', plain,
% 4.18/4.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X16 @ X17)
% 4.18/4.37          | ~ (r1_tarski @ X17 @ X18)
% 4.18/4.37          | (r1_tarski @ X16 @ X18))),
% 4.18/4.37      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.18/4.37  thf('17', plain,
% 4.18/4.37      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['15', '16'])).
% 4.18/4.37  thf('18', plain,
% 4.18/4.37      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['14', '17'])).
% 4.18/4.37  thf(t43_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i,C:$i]:
% 4.18/4.37     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 4.18/4.37       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 4.18/4.37  thf('19', plain,
% 4.18/4.37      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.18/4.37         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 4.18/4.37          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 4.18/4.37      inference('cnf', [status(esa)], [t43_xboole_1])).
% 4.18/4.37  thf('20', plain,
% 4.18/4.37      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0)),
% 4.18/4.37      inference('sup-', [status(thm)], ['18', '19'])).
% 4.18/4.37  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.18/4.37  thf('21', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 4.18/4.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.18/4.37  thf('22', plain,
% 4.18/4.37      (![X7 : $i, X9 : $i]:
% 4.18/4.37         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.18/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.18/4.37  thf('23', plain,
% 4.18/4.37      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['21', '22'])).
% 4.18/4.37  thf('24', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['20', '23'])).
% 4.18/4.37  thf(t15_relat_1, axiom,
% 4.18/4.37    (![A:$i]:
% 4.18/4.37     ( ( v1_relat_1 @ A ) =>
% 4.18/4.37       ( ![B:$i]:
% 4.18/4.37         ( ( v1_relat_1 @ B ) =>
% 4.18/4.37           ( r1_tarski @
% 4.18/4.37             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 4.18/4.37             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 4.18/4.37  thf('25', plain,
% 4.18/4.37      (![X50 : $i, X51 : $i]:
% 4.18/4.37         (~ (v1_relat_1 @ X50)
% 4.18/4.37          | (r1_tarski @ 
% 4.18/4.37             (k6_subset_1 @ (k1_relat_1 @ X51) @ (k1_relat_1 @ X50)) @ 
% 4.18/4.37             (k1_relat_1 @ (k6_subset_1 @ X51 @ X50)))
% 4.18/4.37          | ~ (v1_relat_1 @ X51))),
% 4.18/4.37      inference('cnf', [status(esa)], [t15_relat_1])).
% 4.18/4.37  thf(redefinition_k6_subset_1, axiom,
% 4.18/4.37    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.18/4.37  thf('26', plain,
% 4.18/4.37      (![X38 : $i, X39 : $i]:
% 4.18/4.37         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 4.18/4.37      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.18/4.37  thf('27', plain,
% 4.18/4.37      (![X38 : $i, X39 : $i]:
% 4.18/4.37         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 4.18/4.37      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.18/4.37  thf('28', plain,
% 4.18/4.37      (![X50 : $i, X51 : $i]:
% 4.18/4.37         (~ (v1_relat_1 @ X50)
% 4.18/4.37          | (r1_tarski @ 
% 4.18/4.37             (k4_xboole_0 @ (k1_relat_1 @ X51) @ (k1_relat_1 @ X50)) @ 
% 4.18/4.37             (k1_relat_1 @ (k4_xboole_0 @ X51 @ X50)))
% 4.18/4.37          | ~ (v1_relat_1 @ X51))),
% 4.18/4.37      inference('demod', [status(thm)], ['25', '26', '27'])).
% 4.18/4.37  thf('29', plain,
% 4.18/4.37      (![X7 : $i, X9 : $i]:
% 4.18/4.37         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.18/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.18/4.37  thf('30', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         (~ (v1_relat_1 @ X1)
% 4.18/4.37          | ~ (v1_relat_1 @ X0)
% 4.18/4.37          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.18/4.37               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 4.18/4.37          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 4.18/4.37              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 4.18/4.37      inference('sup-', [status(thm)], ['28', '29'])).
% 4.18/4.37  thf('31', plain,
% 4.18/4.37      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 4.18/4.37           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 4.18/4.37        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 4.18/4.37            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 4.18/4.37        | ~ (v1_relat_1 @ sk_B_1)
% 4.18/4.37        | ~ (v1_relat_1 @ sk_A))),
% 4.18/4.37      inference('sup-', [status(thm)], ['24', '30'])).
% 4.18/4.37  thf(d4_relat_1, axiom,
% 4.18/4.37    (![A:$i,B:$i]:
% 4.18/4.37     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 4.18/4.37       ( ![C:$i]:
% 4.18/4.37         ( ( r2_hidden @ C @ B ) <=>
% 4.18/4.37           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 4.18/4.37  thf('32', plain,
% 4.18/4.37      (![X44 : $i, X47 : $i]:
% 4.18/4.37         (((X47) = (k1_relat_1 @ X44))
% 4.18/4.37          | (r2_hidden @ 
% 4.18/4.37             (k4_tarski @ (sk_C_1 @ X47 @ X44) @ (sk_D @ X47 @ X44)) @ X44)
% 4.18/4.37          | (r2_hidden @ (sk_C_1 @ X47 @ X44) @ X47))),
% 4.18/4.37      inference('cnf', [status(esa)], [d4_relat_1])).
% 4.18/4.37  thf('33', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 4.18/4.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.18/4.37  thf(t28_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i]:
% 4.18/4.37     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.18/4.37  thf('34', plain,
% 4.18/4.37      (![X19 : $i, X20 : $i]:
% 4.18/4.37         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 4.18/4.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.18/4.37  thf('35', plain,
% 4.18/4.37      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['33', '34'])).
% 4.18/4.37  thf(t4_xboole_0, axiom,
% 4.18/4.37    (![A:$i,B:$i]:
% 4.18/4.37     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.18/4.37            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.18/4.37       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.18/4.37            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.18/4.37  thf('36', plain,
% 4.18/4.37      (![X2 : $i, X4 : $i, X5 : $i]:
% 4.18/4.37         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 4.18/4.37          | ~ (r1_xboole_0 @ X2 @ X5))),
% 4.18/4.37      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.18/4.37  thf('37', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['35', '36'])).
% 4.18/4.37  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 4.18/4.37  thf('38', plain, (![X28 : $i]: (r1_xboole_0 @ X28 @ k1_xboole_0)),
% 4.18/4.37      inference('cnf', [status(esa)], [t65_xboole_1])).
% 4.18/4.37  thf(symmetry_r1_xboole_0, axiom,
% 4.18/4.37    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.18/4.37  thf('39', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.18/4.37      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.18/4.37  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.18/4.37      inference('sup-', [status(thm)], ['38', '39'])).
% 4.18/4.37  thf('41', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 4.18/4.37      inference('demod', [status(thm)], ['37', '40'])).
% 4.18/4.37  thf('42', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 4.18/4.37          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['32', '41'])).
% 4.18/4.37  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 4.18/4.37      inference('demod', [status(thm)], ['37', '40'])).
% 4.18/4.37  thf('44', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['42', '43'])).
% 4.18/4.37  thf('45', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 4.18/4.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.18/4.37  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['20', '23'])).
% 4.18/4.37  thf('47', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['42', '43'])).
% 4.18/4.37  thf('48', plain, ((v1_relat_1 @ sk_B_1)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('50', plain,
% 4.18/4.37      (((k1_xboole_0)
% 4.18/4.37         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 4.18/4.37      inference('demod', [status(thm)],
% 4.18/4.37                ['31', '44', '45', '46', '47', '48', '49'])).
% 4.18/4.37  thf('51', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.18/4.37      inference('simplify', [status(thm)], ['9'])).
% 4.18/4.37  thf(t44_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i,C:$i]:
% 4.18/4.37     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 4.18/4.37       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.18/4.37  thf('52', plain,
% 4.18/4.37      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.18/4.37         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 4.18/4.37          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 4.18/4.37      inference('cnf', [status(esa)], [t44_xboole_1])).
% 4.18/4.37  thf('53', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['51', '52'])).
% 4.18/4.37  thf('54', plain,
% 4.18/4.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X16 @ X17)
% 4.18/4.37          | ~ (r1_tarski @ X17 @ X18)
% 4.18/4.37          | (r1_tarski @ X16 @ X18))),
% 4.18/4.37      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.18/4.37  thf('55', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.18/4.37         ((r1_tarski @ X1 @ X2)
% 4.18/4.37          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 4.18/4.37      inference('sup-', [status(thm)], ['53', '54'])).
% 4.18/4.37  thf('56', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0) @ 
% 4.18/4.37             X0)
% 4.18/4.37          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['50', '55'])).
% 4.18/4.37  thf('57', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 4.18/4.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.18/4.37  thf('58', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.18/4.37      inference('simplify', [status(thm)], ['9'])).
% 4.18/4.37  thf(t8_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i,C:$i]:
% 4.18/4.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.18/4.37       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.18/4.37  thf('59', plain,
% 4.18/4.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X31 @ X32)
% 4.18/4.37          | ~ (r1_tarski @ X33 @ X32)
% 4.18/4.37          | (r1_tarski @ (k2_xboole_0 @ X31 @ X33) @ X32))),
% 4.18/4.37      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.18/4.37  thf('60', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['58', '59'])).
% 4.18/4.37  thf('61', plain,
% 4.18/4.37      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 4.18/4.37      inference('sup-', [status(thm)], ['57', '60'])).
% 4.18/4.37  thf('62', plain,
% 4.18/4.37      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 4.18/4.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.18/4.37  thf('63', plain,
% 4.18/4.37      (![X7 : $i, X9 : $i]:
% 4.18/4.37         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.18/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.18/4.37  thf('64', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.18/4.37          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['62', '63'])).
% 4.18/4.37  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['61', '64'])).
% 4.18/4.37  thf('66', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 4.18/4.37          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 4.18/4.37      inference('demod', [status(thm)], ['56', '65'])).
% 4.18/4.37  thf('67', plain,
% 4.18/4.37      ((~ (v1_relat_1 @ sk_B_1)
% 4.18/4.37        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['13', '66'])).
% 4.18/4.37  thf('68', plain, ((v1_relat_1 @ sk_B_1)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('69', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('demod', [status(thm)], ['67', '68'])).
% 4.18/4.37  thf('70', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['58', '59'])).
% 4.18/4.37  thf('71', plain,
% 4.18/4.37      ((r1_tarski @ 
% 4.18/4.37        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 4.18/4.37        (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['69', '70'])).
% 4.18/4.37  thf('72', plain,
% 4.18/4.37      (![X49 : $i]:
% 4.18/4.37         (((k3_relat_1 @ X49)
% 4.18/4.37            = (k2_xboole_0 @ (k2_relat_1 @ X49) @ (k1_relat_1 @ X49)))
% 4.18/4.37          | ~ (v1_relat_1 @ X49))),
% 4.18/4.37      inference('demod', [status(thm)], ['1', '6'])).
% 4.18/4.37  thf('73', plain,
% 4.18/4.37      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 4.18/4.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.18/4.37  thf(t11_xboole_1, axiom,
% 4.18/4.37    (![A:$i,B:$i,C:$i]:
% 4.18/4.37     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 4.18/4.37  thf('74', plain,
% 4.18/4.37      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.18/4.37         ((r1_tarski @ X13 @ X14)
% 4.18/4.37          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 4.18/4.37      inference('cnf', [status(esa)], [t11_xboole_1])).
% 4.18/4.37  thf('75', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.18/4.37         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['73', '74'])).
% 4.18/4.37  thf('76', plain,
% 4.18/4.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X16 @ X17)
% 4.18/4.37          | ~ (r1_tarski @ X17 @ X18)
% 4.18/4.37          | (r1_tarski @ X16 @ X18))),
% 4.18/4.37      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.18/4.37  thf('77', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.18/4.37         ((r1_tarski @ X2 @ X3)
% 4.18/4.37          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3))),
% 4.18/4.37      inference('sup-', [status(thm)], ['75', '76'])).
% 4.18/4.37  thf('78', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ X2) @ X1)
% 4.18/4.37          | ~ (v1_relat_1 @ X0)
% 4.18/4.37          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['72', '77'])).
% 4.18/4.37  thf('79', plain,
% 4.18/4.37      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 4.18/4.37        | ~ (v1_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['71', '78'])).
% 4.18/4.37  thf('80', plain, ((v1_relat_1 @ sk_B_1)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('81', plain,
% 4.18/4.37      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('demod', [status(thm)], ['79', '80'])).
% 4.18/4.37  thf('82', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.18/4.37      inference('simplify', [status(thm)], ['9'])).
% 4.18/4.37  thf('83', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('84', plain,
% 4.18/4.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X31 @ X32)
% 4.18/4.37          | ~ (r1_tarski @ X33 @ X32)
% 4.18/4.37          | (r1_tarski @ (k2_xboole_0 @ X31 @ X33) @ X32))),
% 4.18/4.37      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.18/4.37  thf('85', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 4.18/4.37          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['83', '84'])).
% 4.18/4.37  thf('86', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)),
% 4.18/4.37      inference('sup-', [status(thm)], ['82', '85'])).
% 4.18/4.37  thf('87', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.18/4.37      inference('sup-', [status(thm)], ['10', '11'])).
% 4.18/4.37  thf('88', plain,
% 4.18/4.37      (![X7 : $i, X9 : $i]:
% 4.18/4.37         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.18/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.18/4.37  thf('89', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.18/4.37          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['87', '88'])).
% 4.18/4.37  thf('90', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['86', '89'])).
% 4.18/4.37  thf(t26_relat_1, axiom,
% 4.18/4.37    (![A:$i]:
% 4.18/4.37     ( ( v1_relat_1 @ A ) =>
% 4.18/4.37       ( ![B:$i]:
% 4.18/4.37         ( ( v1_relat_1 @ B ) =>
% 4.18/4.37           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 4.18/4.37             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 4.18/4.37  thf('91', plain,
% 4.18/4.37      (![X52 : $i, X53 : $i]:
% 4.18/4.37         (~ (v1_relat_1 @ X52)
% 4.18/4.37          | ((k2_relat_1 @ (k2_xboole_0 @ X53 @ X52))
% 4.18/4.37              = (k2_xboole_0 @ (k2_relat_1 @ X53) @ (k2_relat_1 @ X52)))
% 4.18/4.37          | ~ (v1_relat_1 @ X53))),
% 4.18/4.37      inference('cnf', [status(esa)], [t26_relat_1])).
% 4.18/4.37  thf('92', plain,
% 4.18/4.37      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.18/4.37         ((r1_tarski @ X13 @ X14)
% 4.18/4.37          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 4.18/4.37      inference('cnf', [status(esa)], [t11_xboole_1])).
% 4.18/4.37  thf('93', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 4.18/4.37          | ~ (v1_relat_1 @ X1)
% 4.18/4.37          | ~ (v1_relat_1 @ X0)
% 4.18/4.37          | (r1_tarski @ (k2_relat_1 @ X1) @ X2))),
% 4.18/4.37      inference('sup-', [status(thm)], ['91', '92'])).
% 4.18/4.37  thf('94', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0)
% 4.18/4.37          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 4.18/4.37          | ~ (v1_relat_1 @ sk_B_1)
% 4.18/4.37          | ~ (v1_relat_1 @ sk_A))),
% 4.18/4.37      inference('sup-', [status(thm)], ['90', '93'])).
% 4.18/4.37  thf('95', plain, ((v1_relat_1 @ sk_B_1)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('97', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         (~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0)
% 4.18/4.37          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 4.18/4.37      inference('demod', [status(thm)], ['94', '95', '96'])).
% 4.18/4.37  thf('98', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['81', '97'])).
% 4.18/4.37  thf('99', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('demod', [status(thm)], ['67', '68'])).
% 4.18/4.37  thf('100', plain,
% 4.18/4.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.18/4.37         (~ (r1_tarski @ X31 @ X32)
% 4.18/4.37          | ~ (r1_tarski @ X33 @ X32)
% 4.18/4.37          | (r1_tarski @ (k2_xboole_0 @ X31 @ X33) @ X32))),
% 4.18/4.37      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.18/4.37  thf('101', plain,
% 4.18/4.37      (![X0 : $i]:
% 4.18/4.37         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 4.18/4.37           (k3_relat_1 @ sk_B_1))
% 4.18/4.37          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 4.18/4.37      inference('sup-', [status(thm)], ['99', '100'])).
% 4.18/4.37  thf('102', plain,
% 4.18/4.37      ((r1_tarski @ 
% 4.18/4.37        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 4.18/4.37        (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('sup-', [status(thm)], ['98', '101'])).
% 4.18/4.37  thf('103', plain,
% 4.18/4.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.18/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.18/4.37  thf('104', plain,
% 4.18/4.37      ((r1_tarski @ 
% 4.18/4.37        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 4.18/4.37        (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('demod', [status(thm)], ['102', '103'])).
% 4.18/4.37  thf('105', plain,
% 4.18/4.37      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 4.18/4.37        | ~ (v1_relat_1 @ sk_A))),
% 4.18/4.37      inference('sup+', [status(thm)], ['7', '104'])).
% 4.18/4.37  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 4.18/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.18/4.37  thf('107', plain,
% 4.18/4.37      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 4.18/4.37      inference('demod', [status(thm)], ['105', '106'])).
% 4.18/4.37  thf('108', plain, ($false), inference('demod', [status(thm)], ['0', '107'])).
% 4.18/4.37  
% 4.18/4.37  % SZS output end Refutation
% 4.18/4.37  
% 4.18/4.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
