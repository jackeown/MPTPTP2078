%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0440+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ln3lBlB2O

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:55 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 363 expanded)
%              Number of leaves         :   20 ( 100 expanded)
%              Depth                    :   25
%              Number of atoms          :  847 (4352 expanded)
%              Number of equality atoms :  103 ( 651 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('0',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X17 @ X14 ) @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_tarski @ ( sk_D_2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( ( k4_tarski @ X20 @ X22 )
       != ( k4_tarski @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('10',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( '#_fresh_sk2' @ X0 )
        = ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( '#_fresh_sk2' @ X1 )
        = ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( '#_fresh_sk2' @ X0 )
       != X1 )
      | ( ( sk_C_2 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( '#_fresh_sk2' @ X0 ) )
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ ( '#_fresh_sk2' @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( '#_fresh_sk2' @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) ) ) @ sk_C_3 )
      = ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) ) )
    | ( ( k1_tarski @ ( '#_fresh_sk2' @ ( k4_tarski @ sk_A @ sk_B ) ) )
      = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('18',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('19',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(inj_rec,[status(thm)],['9'])).

thf('20',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 = X19 )
      | ( ( k4_tarski @ X20 @ X22 )
       != ( k4_tarski @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('27',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X20 @ X22 ) )
      = X20 ) ),
    inference(inj_rec,[status(thm)],['26'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X7 ) @ ( sk_D @ X10 @ X7 ) ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('29',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X20 @ X22 ) )
      = X20 ) ),
    inference(inj_rec,[status(thm)],['26'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( '#_fresh_sk1' @ X0 )
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( '#_fresh_sk1' @ X1 )
        = ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( '#_fresh_sk1' @ X0 )
       != X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( '#_fresh_sk1' @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( '#_fresh_sk1' @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( '#_fresh_sk1' @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( '#_fresh_sk1' @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ ( '#_fresh_sk1' @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X20 @ X22 ) )
      = X20 ) ),
    inference(inj_rec,[status(thm)],['26'])).

thf('39',plain,(
    ! [X20: $i,X22: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X20 @ X22 ) )
      = X20 ) ),
    inference(inj_rec,[status(thm)],['26'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('42',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X7 ) @ X11 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['24','49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('52',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['23','55'])).

thf('57',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['21','56'])).

thf('58',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k2_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_C_2 @ X17 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['21','56'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['23','55'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','64'])).


%------------------------------------------------------------------------------
