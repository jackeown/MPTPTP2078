%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lSKvDkBEHU

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:54 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 976 expanded)
%              Number of leaves         :   45 ( 330 expanded)
%              Depth                    :   33
%              Number of atoms          : 1566 (7278 expanded)
%              Number of equality atoms :   63 ( 372 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X15 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X52 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X52 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('24',plain,(
    ! [X45: $i,X48: $i] :
      ( ( X48
        = ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X48 @ X45 ) @ ( sk_D_1 @ X48 @ X45 ) ) @ X45 )
      | ( r2_hidden @ ( sk_C_1 @ X48 @ X45 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('30',plain,(
    ! [X28: $i] :
      ( r1_xboole_0 @ X28 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('43',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['12','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('52',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('53',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X31 @ X33 ) ) @ X32 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('58',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('64',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('75',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('77',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('79',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('80',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('81',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('82',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['78','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('87',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('88',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('89',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('90',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('91',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('92',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('100',plain,(
    r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('102',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X31 @ X33 ) ) @ X32 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('107',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    r1_tarski @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('112',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k3_relat_1 @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k3_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','117'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('119',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('120',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('121',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('122',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X53 ) @ ( k1_relat_1 @ X53 ) )
      | ~ ( r2_hidden @ X54 @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('130',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['119','130'])).

thf('132',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['118','131'])).

thf('133',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('134',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['134','139'])).

thf('141',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X15 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['77','142'])).

thf('144',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('145',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','36'])).

thf('151',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('152',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('154',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X15 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X31 @ X33 ) ) @ X32 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) )
      | ~ ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['149','158'])).

thf('160',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('161',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('168',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('170',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('172',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('174',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['159','174'])).

thf('176',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['0','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lSKvDkBEHU
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:45:18 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.83/3.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.83/3.08  % Solved by: fo/fo7.sh
% 2.83/3.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.83/3.08  % done 5436 iterations in 2.638s
% 2.83/3.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.83/3.08  % SZS output start Refutation
% 2.83/3.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.83/3.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.83/3.08  thf(sk_B_type, type, sk_B: $i > $i).
% 2.83/3.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.83/3.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.83/3.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.83/3.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.83/3.08  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.83/3.08  thf(sk_A_type, type, sk_A: $i).
% 2.83/3.08  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.83/3.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.83/3.08  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.83/3.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.83/3.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.83/3.08  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.83/3.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.83/3.08  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.83/3.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.83/3.08  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.83/3.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.83/3.08  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 2.83/3.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.83/3.08  thf(t31_relat_1, conjecture,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( v1_relat_1 @ A ) =>
% 2.83/3.08       ( ![B:$i]:
% 2.83/3.08         ( ( v1_relat_1 @ B ) =>
% 2.83/3.08           ( ( r1_tarski @ A @ B ) =>
% 2.83/3.08             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.83/3.08  thf(zf_stmt_0, negated_conjecture,
% 2.83/3.08    (~( ![A:$i]:
% 2.83/3.08        ( ( v1_relat_1 @ A ) =>
% 2.83/3.08          ( ![B:$i]:
% 2.83/3.08            ( ( v1_relat_1 @ B ) =>
% 2.83/3.08              ( ( r1_tarski @ A @ B ) =>
% 2.83/3.08                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 2.83/3.08    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 2.83/3.08  thf('0', plain,
% 2.83/3.08      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf(d6_relat_1, axiom,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( v1_relat_1 @ A ) =>
% 2.83/3.08       ( ( k3_relat_1 @ A ) =
% 2.83/3.08         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.83/3.08  thf('1', plain,
% 2.83/3.08      (![X50 : $i]:
% 2.83/3.08         (((k3_relat_1 @ X50)
% 2.83/3.08            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 2.83/3.08          | ~ (v1_relat_1 @ X50))),
% 2.83/3.08      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.83/3.08  thf(l51_zfmisc_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.83/3.08  thf('2', plain,
% 2.83/3.08      (![X36 : $i, X37 : $i]:
% 2.83/3.08         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 2.83/3.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.83/3.08  thf('3', plain,
% 2.83/3.08      (![X50 : $i]:
% 2.83/3.08         (((k3_relat_1 @ X50)
% 2.83/3.08            = (k3_tarski @ 
% 2.83/3.08               (k2_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 2.83/3.08          | ~ (v1_relat_1 @ X50))),
% 2.83/3.08      inference('demod', [status(thm)], ['1', '2'])).
% 2.83/3.08  thf('4', plain,
% 2.83/3.08      (![X50 : $i]:
% 2.83/3.08         (((k3_relat_1 @ X50)
% 2.83/3.08            = (k3_tarski @ 
% 2.83/3.08               (k2_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 2.83/3.08          | ~ (v1_relat_1 @ X50))),
% 2.83/3.08      inference('demod', [status(thm)], ['1', '2'])).
% 2.83/3.08  thf(d10_xboole_0, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.83/3.08  thf('5', plain,
% 2.83/3.08      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 2.83/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.08  thf('6', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.83/3.08      inference('simplify', [status(thm)], ['5'])).
% 2.83/3.08  thf(t10_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i,C:$i]:
% 2.83/3.08     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.83/3.08  thf('7', plain,
% 2.83/3.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X13 @ X14)
% 2.83/3.08          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 2.83/3.08      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.83/3.08  thf('8', plain,
% 2.83/3.08      (![X36 : $i, X37 : $i]:
% 2.83/3.08         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 2.83/3.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.83/3.08  thf('9', plain,
% 2.83/3.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X13 @ X14)
% 2.83/3.08          | (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X15 @ X14))))),
% 2.83/3.08      inference('demod', [status(thm)], ['7', '8'])).
% 2.83/3.08  thf('10', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['6', '9'])).
% 2.83/3.08  thf('11', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.83/3.08          | ~ (v1_relat_1 @ X0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['4', '10'])).
% 2.83/3.08  thf('12', plain,
% 2.83/3.08      (![X50 : $i]:
% 2.83/3.08         (((k3_relat_1 @ X50)
% 2.83/3.08            = (k3_tarski @ 
% 2.83/3.08               (k2_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 2.83/3.08          | ~ (v1_relat_1 @ X50))),
% 2.83/3.08      inference('demod', [status(thm)], ['1', '2'])).
% 2.83/3.08  thf('13', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf(l32_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.83/3.08  thf('14', plain,
% 2.83/3.08      (![X10 : $i, X12 : $i]:
% 2.83/3.08         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 2.83/3.08          | ~ (r1_tarski @ X10 @ X12))),
% 2.83/3.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.83/3.08  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['13', '14'])).
% 2.83/3.08  thf(t15_relat_1, axiom,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( v1_relat_1 @ A ) =>
% 2.83/3.08       ( ![B:$i]:
% 2.83/3.08         ( ( v1_relat_1 @ B ) =>
% 2.83/3.08           ( r1_tarski @
% 2.83/3.08             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 2.83/3.08             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.83/3.08  thf('16', plain,
% 2.83/3.08      (![X51 : $i, X52 : $i]:
% 2.83/3.08         (~ (v1_relat_1 @ X51)
% 2.83/3.08          | (r1_tarski @ 
% 2.83/3.08             (k6_subset_1 @ (k1_relat_1 @ X52) @ (k1_relat_1 @ X51)) @ 
% 2.83/3.08             (k1_relat_1 @ (k6_subset_1 @ X52 @ X51)))
% 2.83/3.08          | ~ (v1_relat_1 @ X52))),
% 2.83/3.08      inference('cnf', [status(esa)], [t15_relat_1])).
% 2.83/3.08  thf(redefinition_k6_subset_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.83/3.08  thf('17', plain,
% 2.83/3.08      (![X38 : $i, X39 : $i]:
% 2.83/3.08         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.83/3.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.83/3.08  thf('18', plain,
% 2.83/3.08      (![X38 : $i, X39 : $i]:
% 2.83/3.08         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.83/3.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.83/3.08  thf('19', plain,
% 2.83/3.08      (![X51 : $i, X52 : $i]:
% 2.83/3.08         (~ (v1_relat_1 @ X51)
% 2.83/3.08          | (r1_tarski @ 
% 2.83/3.08             (k4_xboole_0 @ (k1_relat_1 @ X52) @ (k1_relat_1 @ X51)) @ 
% 2.83/3.08             (k1_relat_1 @ (k4_xboole_0 @ X52 @ X51)))
% 2.83/3.08          | ~ (v1_relat_1 @ X52))),
% 2.83/3.08      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.83/3.08  thf('20', plain,
% 2.83/3.08      (((r1_tarski @ 
% 2.83/3.08         (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.83/3.08         (k1_relat_1 @ k1_xboole_0))
% 2.83/3.08        | ~ (v1_relat_1 @ sk_A)
% 2.83/3.08        | ~ (v1_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup+', [status(thm)], ['15', '19'])).
% 2.83/3.08  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('22', plain, ((v1_relat_1 @ sk_B_1)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('23', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        (k1_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.83/3.08  thf(d4_relat_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 2.83/3.08       ( ![C:$i]:
% 2.83/3.08         ( ( r2_hidden @ C @ B ) <=>
% 2.83/3.08           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 2.83/3.08  thf('24', plain,
% 2.83/3.08      (![X45 : $i, X48 : $i]:
% 2.83/3.08         (((X48) = (k1_relat_1 @ X45))
% 2.83/3.08          | (r2_hidden @ 
% 2.83/3.08             (k4_tarski @ (sk_C_1 @ X48 @ X45) @ (sk_D_1 @ X48 @ X45)) @ X45)
% 2.83/3.08          | (r2_hidden @ (sk_C_1 @ X48 @ X45) @ X48))),
% 2.83/3.08      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.83/3.08  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.83/3.08  thf('25', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.83/3.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.08  thf(t28_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.83/3.08  thf('26', plain,
% 2.83/3.08      (![X19 : $i, X20 : $i]:
% 2.83/3.08         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.83/3.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.83/3.08  thf('27', plain,
% 2.83/3.08      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['25', '26'])).
% 2.83/3.08  thf(t4_xboole_0, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.83/3.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.83/3.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.83/3.08            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.83/3.08  thf('28', plain,
% 2.83/3.08      (![X2 : $i, X4 : $i, X5 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 2.83/3.08          | ~ (r1_xboole_0 @ X2 @ X5))),
% 2.83/3.08      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.83/3.08  thf('29', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['27', '28'])).
% 2.83/3.08  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.83/3.08  thf('30', plain, (![X28 : $i]: (r1_xboole_0 @ X28 @ k1_xboole_0)),
% 2.83/3.08      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.83/3.08  thf(symmetry_r1_xboole_0, axiom,
% 2.83/3.08    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.83/3.08  thf('31', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.83/3.08      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.83/3.08  thf('32', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.83/3.08      inference('sup-', [status(thm)], ['30', '31'])).
% 2.83/3.08  thf('33', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.83/3.08      inference('demod', [status(thm)], ['29', '32'])).
% 2.83/3.08  thf('34', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 2.83/3.08          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['24', '33'])).
% 2.83/3.08  thf('35', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.83/3.08      inference('demod', [status(thm)], ['29', '32'])).
% 2.83/3.08  thf('36', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['34', '35'])).
% 2.83/3.08  thf('37', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        k1_xboole_0)),
% 2.83/3.08      inference('demod', [status(thm)], ['23', '36'])).
% 2.83/3.08  thf('38', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.83/3.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.08  thf('39', plain,
% 2.83/3.08      (![X7 : $i, X9 : $i]:
% 2.83/3.08         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.83/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.08  thf('40', plain,
% 2.83/3.08      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['38', '39'])).
% 2.83/3.08  thf('41', plain,
% 2.83/3.08      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 2.83/3.08         = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['37', '40'])).
% 2.83/3.08  thf(t44_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i,C:$i]:
% 2.83/3.08     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 2.83/3.08       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.83/3.08  thf('42', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('cnf', [status(esa)], [t44_xboole_1])).
% 2.83/3.08  thf('43', plain,
% 2.83/3.08      (![X36 : $i, X37 : $i]:
% 2.83/3.08         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 2.83/3.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.83/3.08  thf('44', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('45', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.83/3.08          | (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.83/3.08             (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ X0))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['41', '44'])).
% 2.83/3.08  thf('46', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.83/3.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.08  thf('47', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.83/3.08          (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ X0)))),
% 2.83/3.08      inference('demod', [status(thm)], ['45', '46'])).
% 2.83/3.08  thf('48', plain,
% 2.83/3.08      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.83/3.08        | ~ (v1_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup+', [status(thm)], ['12', '47'])).
% 2.83/3.08  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('50', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['48', '49'])).
% 2.83/3.08  thf('51', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.83/3.08      inference('simplify', [status(thm)], ['5'])).
% 2.83/3.08  thf(t8_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i,C:$i]:
% 2.83/3.08     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.83/3.08       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.83/3.08  thf('52', plain,
% 2.83/3.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X31 @ X32)
% 2.83/3.08          | ~ (r1_tarski @ X33 @ X32)
% 2.83/3.08          | (r1_tarski @ (k2_xboole_0 @ X31 @ X33) @ X32))),
% 2.83/3.08      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.83/3.08  thf('53', plain,
% 2.83/3.08      (![X36 : $i, X37 : $i]:
% 2.83/3.08         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 2.83/3.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.83/3.08  thf('54', plain,
% 2.83/3.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X31 @ X32)
% 2.83/3.08          | ~ (r1_tarski @ X33 @ X32)
% 2.83/3.08          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X31 @ X33)) @ X32))),
% 2.83/3.08      inference('demod', [status(thm)], ['52', '53'])).
% 2.83/3.08  thf('55', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 2.83/3.08          | ~ (r1_tarski @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['51', '54'])).
% 2.83/3.08  thf('56', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))) @ 
% 2.83/3.08        (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['50', '55'])).
% 2.83/3.08  thf(t7_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.83/3.08  thf('57', plain,
% 2.83/3.08      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 2.83/3.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.83/3.08  thf('58', plain,
% 2.83/3.08      (![X36 : $i, X37 : $i]:
% 2.83/3.08         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 2.83/3.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.83/3.08  thf('59', plain,
% 2.83/3.08      (![X29 : $i, X30 : $i]:
% 2.83/3.08         (r1_tarski @ X29 @ (k3_tarski @ (k2_tarski @ X29 @ X30)))),
% 2.83/3.08      inference('demod', [status(thm)], ['57', '58'])).
% 2.83/3.08  thf('60', plain,
% 2.83/3.08      (![X7 : $i, X9 : $i]:
% 2.83/3.08         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.83/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.08  thf('61', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 2.83/3.08          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['59', '60'])).
% 2.83/3.08  thf('62', plain,
% 2.83/3.08      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))
% 2.83/3.08         = (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['56', '61'])).
% 2.83/3.08  thf(t43_xboole_1, axiom,
% 2.83/3.08    (![A:$i,B:$i,C:$i]:
% 2.83/3.08     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.83/3.08       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.83/3.08  thf('63', plain,
% 2.83/3.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.08         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 2.83/3.08          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 2.83/3.08      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.83/3.08  thf('64', plain,
% 2.83/3.08      (![X36 : $i, X37 : $i]:
% 2.83/3.08         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 2.83/3.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.83/3.08  thf('65', plain,
% 2.83/3.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.08         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 2.83/3.08          | ~ (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X23 @ X24))))),
% 2.83/3.08      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.08  thf('66', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1))
% 2.83/3.08          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_relat_1 @ sk_B_1)) @ 
% 2.83/3.08             (k1_relat_1 @ sk_A)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['62', '65'])).
% 2.83/3.08  thf('67', plain,
% 2.83/3.08      ((~ (v1_relat_1 @ sk_B_1)
% 2.83/3.08        | (r1_tarski @ 
% 2.83/3.08           (k4_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 2.83/3.08           (k1_relat_1 @ sk_A)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['11', '66'])).
% 2.83/3.08  thf('68', plain, ((v1_relat_1 @ sk_B_1)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('69', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        (k1_relat_1 @ sk_A))),
% 2.83/3.08      inference('demod', [status(thm)], ['67', '68'])).
% 2.83/3.08  thf('70', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('71', plain,
% 2.83/3.08      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['69', '70'])).
% 2.83/3.08  thf('72', plain,
% 2.83/3.08      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))
% 2.83/3.08         = (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['56', '61'])).
% 2.83/3.08  thf('73', plain,
% 2.83/3.08      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['71', '72'])).
% 2.83/3.08  thf('74', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 2.83/3.08          | ~ (r1_tarski @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['51', '54'])).
% 2.83/3.08  thf('75', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k3_tarski @ 
% 2.83/3.08         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))) @ 
% 2.83/3.08        (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['73', '74'])).
% 2.83/3.08  thf('76', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 2.83/3.08          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['59', '60'])).
% 2.83/3.08  thf('77', plain,
% 2.83/3.08      (((k3_tarski @ 
% 2.83/3.08         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1)))
% 2.83/3.08         = (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['75', '76'])).
% 2.83/3.08  thf('78', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['13', '14'])).
% 2.83/3.08  thf(t28_relat_1, axiom,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ( v1_relat_1 @ A ) =>
% 2.83/3.08       ( ![B:$i]:
% 2.83/3.08         ( ( v1_relat_1 @ B ) =>
% 2.83/3.08           ( r1_tarski @
% 2.83/3.08             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 2.83/3.08             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.83/3.08  thf('79', plain,
% 2.83/3.08      (![X55 : $i, X56 : $i]:
% 2.83/3.08         (~ (v1_relat_1 @ X55)
% 2.83/3.08          | (r1_tarski @ 
% 2.83/3.08             (k6_subset_1 @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55)) @ 
% 2.83/3.08             (k2_relat_1 @ (k6_subset_1 @ X56 @ X55)))
% 2.83/3.08          | ~ (v1_relat_1 @ X56))),
% 2.83/3.08      inference('cnf', [status(esa)], [t28_relat_1])).
% 2.83/3.08  thf('80', plain,
% 2.83/3.08      (![X38 : $i, X39 : $i]:
% 2.83/3.08         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.83/3.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.83/3.08  thf('81', plain,
% 2.83/3.08      (![X38 : $i, X39 : $i]:
% 2.83/3.08         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.83/3.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.83/3.08  thf('82', plain,
% 2.83/3.08      (![X55 : $i, X56 : $i]:
% 2.83/3.08         (~ (v1_relat_1 @ X55)
% 2.83/3.08          | (r1_tarski @ 
% 2.83/3.08             (k4_xboole_0 @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55)) @ 
% 2.83/3.08             (k2_relat_1 @ (k4_xboole_0 @ X56 @ X55)))
% 2.83/3.08          | ~ (v1_relat_1 @ X56))),
% 2.83/3.08      inference('demod', [status(thm)], ['79', '80', '81'])).
% 2.83/3.08  thf('83', plain,
% 2.83/3.08      (((r1_tarski @ 
% 2.83/3.08         (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.83/3.08         (k2_relat_1 @ k1_xboole_0))
% 2.83/3.08        | ~ (v1_relat_1 @ sk_A)
% 2.83/3.08        | ~ (v1_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup+', [status(thm)], ['78', '82'])).
% 2.83/3.08  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('85', plain, ((v1_relat_1 @ sk_B_1)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('86', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        (k2_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['83', '84', '85'])).
% 2.83/3.08  thf(cc1_relat_1, axiom,
% 2.83/3.08    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 2.83/3.08  thf('87', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 2.83/3.08      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.83/3.08  thf('88', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 2.83/3.08      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.83/3.08  thf('89', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['34', '35'])).
% 2.83/3.08  thf('90', plain,
% 2.83/3.08      (![X50 : $i]:
% 2.83/3.08         (((k3_relat_1 @ X50)
% 2.83/3.08            = (k3_tarski @ 
% 2.83/3.08               (k2_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 2.83/3.08          | ~ (v1_relat_1 @ X50))),
% 2.83/3.08      inference('demod', [status(thm)], ['1', '2'])).
% 2.83/3.08  thf('91', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.83/3.08      inference('simplify', [status(thm)], ['5'])).
% 2.83/3.08  thf('92', plain,
% 2.83/3.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.08         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 2.83/3.08          | ~ (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X23 @ X24))))),
% 2.83/3.08      inference('demod', [status(thm)], ['63', '64'])).
% 2.83/3.08  thf('93', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (r1_tarski @ 
% 2.83/3.08          (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1) @ X0)),
% 2.83/3.08      inference('sup-', [status(thm)], ['91', '92'])).
% 2.83/3.08  thf('94', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         ((r1_tarski @ (k4_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 2.83/3.08           (k2_relat_1 @ X0))
% 2.83/3.08          | ~ (v1_relat_1 @ X0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['90', '93'])).
% 2.83/3.08  thf('95', plain,
% 2.83/3.08      (((r1_tarski @ 
% 2.83/3.08         (k4_xboole_0 @ (k3_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.83/3.08         (k2_relat_1 @ k1_xboole_0))
% 2.83/3.08        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['89', '94'])).
% 2.83/3.08  thf('96', plain,
% 2.83/3.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.83/3.08        | (r1_tarski @ 
% 2.83/3.08           (k4_xboole_0 @ (k3_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.83/3.08           (k2_relat_1 @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['88', '95'])).
% 2.83/3.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.83/3.08  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.83/3.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.83/3.08  thf('98', plain,
% 2.83/3.08      ((r1_tarski @ (k4_xboole_0 @ (k3_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 2.83/3.08        (k2_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['96', '97'])).
% 2.83/3.08  thf('99', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('100', plain,
% 2.83/3.08      ((r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['98', '99'])).
% 2.83/3.08  thf('101', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.83/3.08      inference('simplify', [status(thm)], ['5'])).
% 2.83/3.08  thf('102', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.83/3.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.08  thf('103', plain,
% 2.83/3.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X31 @ X32)
% 2.83/3.08          | ~ (r1_tarski @ X33 @ X32)
% 2.83/3.08          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X31 @ X33)) @ X32))),
% 2.83/3.08      inference('demod', [status(thm)], ['52', '53'])).
% 2.83/3.08  thf('104', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_tarski @ (k3_tarski @ (k2_tarski @ k1_xboole_0 @ X1)) @ X0)
% 2.83/3.08          | ~ (r1_tarski @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['102', '103'])).
% 2.83/3.08  thf('105', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (r1_tarski @ (k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) @ X0)),
% 2.83/3.08      inference('sup-', [status(thm)], ['101', '104'])).
% 2.83/3.08  thf('106', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['6', '9'])).
% 2.83/3.08  thf('107', plain,
% 2.83/3.08      (![X7 : $i, X9 : $i]:
% 2.83/3.08         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.83/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.08  thf('108', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X0)
% 2.83/3.08          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['106', '107'])).
% 2.83/3.08  thf('109', plain,
% 2.83/3.08      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['105', '108'])).
% 2.83/3.08  thf('110', plain,
% 2.83/3.08      ((r1_tarski @ (k3_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['100', '109'])).
% 2.83/3.08  thf('111', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.83/3.08          | ~ (v1_relat_1 @ X0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['4', '10'])).
% 2.83/3.08  thf('112', plain,
% 2.83/3.08      (![X7 : $i, X9 : $i]:
% 2.83/3.08         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.83/3.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.83/3.08  thf('113', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (v1_relat_1 @ X0)
% 2.83/3.08          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.83/3.08          | ((k3_relat_1 @ X0) = (k2_relat_1 @ X0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['111', '112'])).
% 2.83/3.08  thf('114', plain,
% 2.83/3.08      ((((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 2.83/3.08        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['110', '113'])).
% 2.83/3.08  thf('115', plain,
% 2.83/3.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.83/3.08        | ((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['87', '114'])).
% 2.83/3.08  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.83/3.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.83/3.08  thf('117', plain,
% 2.83/3.08      (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['115', '116'])).
% 2.83/3.08  thf('118', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        (k3_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['86', '117'])).
% 2.83/3.08  thf(t7_xboole_0, axiom,
% 2.83/3.08    (![A:$i]:
% 2.83/3.08     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.83/3.08          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.83/3.08  thf('119', plain,
% 2.83/3.08      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.83/3.08      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.83/3.08  thf('120', plain,
% 2.83/3.08      (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 2.83/3.08      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.83/3.08  thf('121', plain,
% 2.83/3.08      (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['115', '116'])).
% 2.83/3.08  thf(t19_relat_1, axiom,
% 2.83/3.08    (![A:$i,B:$i]:
% 2.83/3.08     ( ( v1_relat_1 @ B ) =>
% 2.83/3.08       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 2.83/3.08            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 2.83/3.08  thf('122', plain,
% 2.83/3.08      (![X53 : $i, X54 : $i]:
% 2.83/3.08         ((r2_hidden @ (sk_C_2 @ X53) @ (k1_relat_1 @ X53))
% 2.83/3.08          | ~ (r2_hidden @ X54 @ (k2_relat_1 @ X53))
% 2.83/3.08          | ~ (v1_relat_1 @ X53))),
% 2.83/3.08      inference('cnf', [status(esa)], [t19_relat_1])).
% 2.83/3.08  thf('123', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))
% 2.83/3.08          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.83/3.08          | (r2_hidden @ (sk_C_2 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['121', '122'])).
% 2.83/3.08  thf('124', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['34', '35'])).
% 2.83/3.08  thf('125', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))
% 2.83/3.08          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.83/3.08          | (r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['123', '124'])).
% 2.83/3.08  thf('126', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.83/3.08      inference('demod', [status(thm)], ['29', '32'])).
% 2.83/3.08  thf('127', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (v1_relat_1 @ k1_xboole_0)
% 2.83/3.08          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)))),
% 2.83/3.08      inference('clc', [status(thm)], ['125', '126'])).
% 2.83/3.08  thf('128', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.83/3.08          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['120', '127'])).
% 2.83/3.08  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.83/3.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.83/3.08  thf('130', plain,
% 2.83/3.08      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))),
% 2.83/3.08      inference('demod', [status(thm)], ['128', '129'])).
% 2.83/3.08  thf('131', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['119', '130'])).
% 2.83/3.08  thf('132', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        k1_xboole_0)),
% 2.83/3.08      inference('demod', [status(thm)], ['118', '131'])).
% 2.83/3.08  thf('133', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('134', plain,
% 2.83/3.08      ((r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k2_relat_1 @ sk_B_1) @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['132', '133'])).
% 2.83/3.08  thf('135', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.83/3.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.08  thf('136', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 2.83/3.08          | ~ (r1_tarski @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['51', '54'])).
% 2.83/3.08  thf('137', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X0)),
% 2.83/3.08      inference('sup-', [status(thm)], ['135', '136'])).
% 2.83/3.08  thf('138', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 2.83/3.08          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['59', '60'])).
% 2.83/3.08  thf('139', plain,
% 2.83/3.08      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['137', '138'])).
% 2.83/3.08  thf('140', plain,
% 2.83/3.08      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['134', '139'])).
% 2.83/3.08  thf('141', plain,
% 2.83/3.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X13 @ X14)
% 2.83/3.08          | (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X15 @ X14))))),
% 2.83/3.08      inference('demod', [status(thm)], ['7', '8'])).
% 2.83/3.08  thf('142', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.83/3.08          (k3_tarski @ (k2_tarski @ X0 @ (k2_relat_1 @ sk_B_1))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['140', '141'])).
% 2.83/3.08  thf('143', plain,
% 2.83/3.08      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup+', [status(thm)], ['77', '142'])).
% 2.83/3.08  thf('144', plain,
% 2.83/3.08      (![X10 : $i, X12 : $i]:
% 2.83/3.08         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 2.83/3.08          | ~ (r1_tarski @ X10 @ X12))),
% 2.83/3.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.83/3.08  thf('145', plain,
% 2.83/3.08      (((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.83/3.08         = (k1_xboole_0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['143', '144'])).
% 2.83/3.08  thf('146', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('147', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 2.83/3.08          | (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.83/3.08             (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ X0))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['145', '146'])).
% 2.83/3.08  thf('148', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 2.83/3.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.83/3.08  thf('149', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.83/3.08          (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ X0)))),
% 2.83/3.08      inference('demod', [status(thm)], ['147', '148'])).
% 2.83/3.08  thf('150', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        k1_xboole_0)),
% 2.83/3.08      inference('demod', [status(thm)], ['23', '36'])).
% 2.83/3.08  thf('151', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('152', plain,
% 2.83/3.08      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['150', '151'])).
% 2.83/3.08  thf('153', plain,
% 2.83/3.08      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['137', '138'])).
% 2.83/3.08  thf('154', plain,
% 2.83/3.08      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['152', '153'])).
% 2.83/3.08  thf('155', plain,
% 2.83/3.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X13 @ X14)
% 2.83/3.08          | (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X15 @ X14))))),
% 2.83/3.08      inference('demod', [status(thm)], ['7', '8'])).
% 2.83/3.08  thf('156', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 2.83/3.08          (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_1))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['154', '155'])).
% 2.83/3.08  thf('157', plain,
% 2.83/3.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X31 @ X32)
% 2.83/3.08          | ~ (r1_tarski @ X33 @ X32)
% 2.83/3.08          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X31 @ X33)) @ X32))),
% 2.83/3.08      inference('demod', [status(thm)], ['52', '53'])).
% 2.83/3.08  thf('158', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ X1)) @ 
% 2.83/3.08           (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_1))))
% 2.83/3.08          | ~ (r1_tarski @ X1 @ 
% 2.83/3.08               (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_1)))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['156', '157'])).
% 2.83/3.08  thf('159', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) @ 
% 2.83/3.08        (k3_tarski @ 
% 2.83/3.08         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['149', '158'])).
% 2.83/3.08  thf('160', plain,
% 2.83/3.08      (![X50 : $i]:
% 2.83/3.08         (((k3_relat_1 @ X50)
% 2.83/3.08            = (k3_tarski @ 
% 2.83/3.08               (k2_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 2.83/3.08          | ~ (v1_relat_1 @ X50))),
% 2.83/3.08      inference('demod', [status(thm)], ['1', '2'])).
% 2.83/3.08  thf('161', plain,
% 2.83/3.08      (![X29 : $i, X30 : $i]:
% 2.83/3.08         (r1_tarski @ X29 @ (k3_tarski @ (k2_tarski @ X29 @ X30)))),
% 2.83/3.08      inference('demod', [status(thm)], ['57', '58'])).
% 2.83/3.08  thf('162', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.83/3.08          | ~ (v1_relat_1 @ X0))),
% 2.83/3.08      inference('sup+', [status(thm)], ['160', '161'])).
% 2.83/3.08  thf('163', plain,
% 2.83/3.08      (![X0 : $i]:
% 2.83/3.08         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1))
% 2.83/3.08          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_relat_1 @ sk_B_1)) @ 
% 2.83/3.08             (k1_relat_1 @ sk_A)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['62', '65'])).
% 2.83/3.08  thf('164', plain,
% 2.83/3.08      ((~ (v1_relat_1 @ sk_B_1)
% 2.83/3.08        | (r1_tarski @ 
% 2.83/3.08           (k4_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 2.83/3.08           (k1_relat_1 @ sk_A)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['162', '163'])).
% 2.83/3.08  thf('165', plain, ((v1_relat_1 @ sk_B_1)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('166', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k4_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 2.83/3.08        (k1_relat_1 @ sk_A))),
% 2.83/3.08      inference('demod', [status(thm)], ['164', '165'])).
% 2.83/3.08  thf('167', plain,
% 2.83/3.08      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.83/3.08         ((r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))
% 2.83/3.08          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 2.83/3.08      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.08  thf('168', plain,
% 2.83/3.08      ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))))),
% 2.83/3.08      inference('sup-', [status(thm)], ['166', '167'])).
% 2.83/3.08  thf('169', plain,
% 2.83/3.08      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))
% 2.83/3.08         = (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['56', '61'])).
% 2.83/3.08  thf('170', plain,
% 2.83/3.08      ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['168', '169'])).
% 2.83/3.08  thf('171', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 2.83/3.08          | ~ (r1_tarski @ X1 @ X0))),
% 2.83/3.08      inference('sup-', [status(thm)], ['51', '54'])).
% 2.83/3.08  thf('172', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k3_tarski @ 
% 2.83/3.08         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1))) @ 
% 2.83/3.08        (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['170', '171'])).
% 2.83/3.08  thf('173', plain,
% 2.83/3.08      (![X0 : $i, X1 : $i]:
% 2.83/3.08         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 2.83/3.08          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 2.83/3.08      inference('sup-', [status(thm)], ['59', '60'])).
% 2.83/3.08  thf('174', plain,
% 2.83/3.08      (((k3_tarski @ 
% 2.83/3.08         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1)))
% 2.83/3.08         = (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('sup-', [status(thm)], ['172', '173'])).
% 2.83/3.08  thf('175', plain,
% 2.83/3.08      ((r1_tarski @ 
% 2.83/3.08        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) @ 
% 2.83/3.08        (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['159', '174'])).
% 2.83/3.08  thf('176', plain,
% 2.83/3.08      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 2.83/3.08        | ~ (v1_relat_1 @ sk_A))),
% 2.83/3.08      inference('sup+', [status(thm)], ['3', '175'])).
% 2.83/3.08  thf('177', plain, ((v1_relat_1 @ sk_A)),
% 2.83/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.08  thf('178', plain,
% 2.83/3.08      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 2.83/3.08      inference('demod', [status(thm)], ['176', '177'])).
% 2.83/3.08  thf('179', plain, ($false), inference('demod', [status(thm)], ['0', '178'])).
% 2.83/3.08  
% 2.83/3.08  % SZS output end Refutation
% 2.83/3.08  
% 2.83/3.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
