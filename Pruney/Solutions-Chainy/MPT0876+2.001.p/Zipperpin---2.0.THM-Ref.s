%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2C10whxGKu

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:19 EST 2020

% Result     : Theorem 47.14s
% Output     : Refutation 47.14s
% Verified   : 
% Statistics : Number of formulae       :  466 (12555 expanded)
%              Number of leaves         :   35 (3944 expanded)
%              Depth                    :   44
%              Number of atoms          : 4063 (114576 expanded)
%              Number of equality atoms :  671 (14380 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X22 @ X19 @ X20 ) @ ( sk_E_1 @ X22 @ X19 @ X20 ) @ X22 @ X19 @ X20 )
      | ( X21
       != ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X22 @ X19 @ X20 ) @ ( sk_E_1 @ X22 @ X19 @ X20 ) @ X22 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X10 @ X14 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('14',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ X3 @ k1_xboole_0 @ X0 )
        = ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t36_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_mcart_1])).

thf('45',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('51',plain,
    ( ( ( k1_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ( ( k1_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('57',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('62',plain,
    ( ( sk_A = sk_D_1 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( sk_E_2 = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_A )
      | ( sk_F_2 = k1_xboole_0 )
      | ( sk_A = sk_D_1 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_E_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( sk_E_2 = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_A )
      | ( sk_F_2 = k1_xboole_0 )
      | ( sk_A = sk_D_1 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_E_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E_2 @ X0 )
      | ( sk_A = sk_D_1 )
      | ( sk_F_2 = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_A )
      | ( sk_E_2 = k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X3 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('78',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X29 @ X28 ) @ ( k2_zfmisc_1 @ X30 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['82'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_A = sk_D_1 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','86'])).

thf('88',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('91',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) )
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) )
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['97','101'])).

thf('103',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('104',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','106'])).

thf('108',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('109',plain,
    ( ( ( k1_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('111',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('112',plain,
    ( ( k1_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('114',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) )
        = X2 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X35 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('118',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_D_1 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_D_1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_A = sk_D_1 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup+',[status(thm)],['88','119'])).

thf('121',plain,
    ( ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_F_2 )
    | ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('125',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('127',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('128',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X3 ) )
      | ( r1_tarski @ X0 @ X3 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X3 ) )
      | ( r1_tarski @ X0 @ X3 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) @ k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,
    ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) @ k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F_2 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['82'])).

thf('136',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A != X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ sk_F_2 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('141',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('142',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('143',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('147',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F_2 ) ),
    inference('sup-',[status(thm)],['140','147'])).

thf('149',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F_2 ) ),
    inference(clc,[status(thm)],['139','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','106'])).

thf('151',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F_2 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','151'])).

thf('153',plain,
    ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','106'])).

thf('154',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('155',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['152','159'])).

thf('161',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('162',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('164',plain,
    ( ( v1_xboole_0 @ sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('166',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('167',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('173',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('174',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('178',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['176','180'])).

thf('182',plain,
    ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','106'])).

thf('183',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
    | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ sk_E_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_D_1 )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_F_2 ) ) ) ),
    inference('sup-',[status(thm)],['164','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( sk_A = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','187'])).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2 ) )
      | ( sk_D_1 = k1_xboole_0 )
      | ( sk_A = sk_D_1 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2 ) )
    | ( sk_A = sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','190'])).

thf('192',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','191'])).

thf('193',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('194',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_A = sk_D_1 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('196',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('198',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = ( k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('202',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X2 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X2 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['200','203'])).

thf('205',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('206',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('207',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ X0 @ X2 ) )
      | ~ ( v1_xboole_0 @ X3 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('210',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_xboole_0 @ X3 )
      | ( ( k3_zfmisc_1 @ X3 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 ) )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['197','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = ( k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('214',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X2 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('215',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X0 )
        = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ k1_xboole_0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('220',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('223',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['218','223'])).

thf('225',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('226',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      | ( ( k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['217','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['216','227'])).

thf('229',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('232',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('233',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['215','230','231','232'])).

thf('234',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('235',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(demod,[status(thm)],['212','233','234'])).

thf('236',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('237',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('239',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    sk_A = sk_D_1 ),
    inference('sup-',[status(thm)],['196','239'])).

thf('241',plain,
    ( ( sk_A != sk_D_1 )
    | ( sk_B_1 != sk_E_2 )
    | ( sk_C_1 != sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('242',plain,
    ( ( sk_A != sk_D_1 )
   <= ( sk_A != sk_D_1 ) ),
    inference(split,[status(esa)],['241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('246',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('247',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('248',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['246','249'])).

thf('251',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('252',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('254',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('256',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('258',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = sk_C_1 ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('260',plain,
    ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    = sk_C_1 ),
    inference(clc,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('262',plain,
    ( ( sk_C_1 = sk_F_2 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('264',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( v1_xboole_0 @ sk_E_2 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('266',plain,
    ( ( sk_F_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( v1_xboole_0 @ sk_E_2 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('268',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('270',plain,
    ( ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('272',plain,
    ( ( v1_xboole_0 @ sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('274',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('276',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['176','180'])).

thf('277',plain,
    ( ~ ( v1_xboole_0 @ sk_F_2 )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( sk_E_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['272','277'])).

thf('279',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('280',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('282',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('284',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('286',plain,
    ( ( v1_xboole_0 @ sk_E_2 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['284','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ sk_E_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','185'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( sk_C_1 = sk_F_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_F_2 ) ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1 = sk_F_2 )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['245','288'])).

thf('290',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('291',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2 ) )
      | ( sk_C_1 = sk_F_2 )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['289','290'])).

thf('292',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2 ) )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 ) ),
    inference('sup-',[status(thm)],['244','291'])).

thf('293',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['243','292'])).

thf('294',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('295',plain,
    ( ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('297',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('298',plain,
    ( ( sk_C_1 = sk_F_2 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('299',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F_2 = k1_xboole_0 )
      | ( sk_C_1 = sk_F_2 ) ) ),
    inference('sup+',[status(thm)],['298','299'])).

thf('301',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('302',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ X0 ) )
      | ( sk_C_1 = sk_F_2 )
      | ( sk_F_2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['300','301'])).

thf('303',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_F_2 = k1_xboole_0 )
      | ( sk_C_1 = sk_F_2 ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2 ) )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_F_2 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['297','304'])).

thf('306',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('307',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2 ) )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_F_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 ) ),
    inference('sup-',[status(thm)],['296','307'])).

thf('309',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('310',plain,
    ( ( sk_F_2 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 ) ),
    inference(demod,[status(thm)],['308','309'])).

thf('311',plain,
    ( ( sk_F_2 = sk_D_1 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_C_1 = sk_F_2 ) ),
    inference('sup+',[status(thm)],['295','310'])).

thf('312',plain,
    ( ( sk_C_1 = sk_F_2 )
    | ( sk_F_2 = sk_D_1 ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,
    ( ( sk_C_1 != sk_F_2 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(split,[status(esa)],['241'])).

thf('314',plain,
    ( ( ( sk_F_2 != sk_F_2 )
      | ( sk_F_2 = sk_D_1 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,
    ( ( sk_F_2 = sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('317',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('318',plain,(
    ~ ( v1_xboole_0 @ sk_F_2 ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('sup-',[status(thm)],['315','318'])).

thf('320',plain,
    ( ( sk_C_1 = sk_F_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('321',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('322',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_F_2 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('323',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_E_2 )
      | ( sk_C_1 = sk_F_2 )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['322','323'])).

thf('325',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = sk_F_2 )
      | ( X0 = sk_E_2 ) ) ),
    inference('sup+',[status(thm)],['324','325'])).

thf('327',plain,
    ( ( k1_xboole_0 = sk_E_2 )
    | ( sk_C_1 = sk_F_2 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['321','326'])).

thf('328',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('sup-',[status(thm)],['315','318'])).

thf('329',plain,
    ( ( ( sk_C_1 = sk_F_2 )
      | ( k1_xboole_0 = sk_E_2 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,
    ( ( sk_F_2 = sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(simplify,[status(thm)],['314'])).

thf('331',plain,
    ( ( ( sk_C_1 = sk_D_1 )
      | ( k1_xboole_0 = sk_E_2 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(demod,[status(thm)],['329','330'])).

thf('332',plain,
    ( ( sk_C_1 != sk_F_2 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(split,[status(esa)],['241'])).

thf('333',plain,
    ( ( sk_F_2 = sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(simplify,[status(thm)],['314'])).

thf('334',plain,
    ( ( sk_C_1 != sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(demod,[status(thm)],['332','333'])).

thf('335',plain,
    ( ( k1_xboole_0 = sk_E_2 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('simplify_reflect-',[status(thm)],['331','334'])).

thf('336',plain,
    ( ( ( sk_D_1 = sk_E_2 )
      | ( sk_C_1 = sk_F_2 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('sup+',[status(thm)],['320','335'])).

thf('337',plain,
    ( ( sk_F_2 = sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(simplify,[status(thm)],['314'])).

thf('338',plain,
    ( ( ( sk_D_1 = sk_E_2 )
      | ( sk_C_1 = sk_D_1 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('339',plain,
    ( ( sk_C_1 != sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(demod,[status(thm)],['332','333'])).

thf('340',plain,
    ( ( sk_D_1 = sk_E_2 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('simplify_reflect-',[status(thm)],['338','339'])).

thf('341',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('342',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = sk_F_2 )
      | ( X0 = sk_E_2 ) ) ),
    inference('sup+',[status(thm)],['324','325'])).

thf('344',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = sk_E_2 )
      | ( sk_C_1 = sk_F_2 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_D_1 )
      | ( sk_C_1 = sk_F_2 )
      | ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
        = sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['341','344'])).

thf('346',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('347',plain,
    ( ( v1_xboole_0 @ sk_E_2 )
    | ( sk_C_1 = sk_F_2 )
    | ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['345','346'])).

thf('348',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('349',plain,
    ( ( v1_xboole_0 @ sk_E_2 )
    | ( sk_C_1 = sk_F_2 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( sk_C_1 = sk_F_2 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('sup+',[status(thm)],['340','349'])).

thf('351',plain,
    ( ( sk_F_2 = sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(simplify,[status(thm)],['314'])).

thf('352',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( sk_C_1 = sk_D_1 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(demod,[status(thm)],['350','351'])).

thf('353',plain,
    ( ( ( sk_C_1 = sk_D_1 )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,
    ( ( sk_C_1 != sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference(demod,[status(thm)],['332','333'])).

thf('355',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
   <= ( sk_C_1 != sk_F_2 ) ),
    inference('simplify_reflect-',[status(thm)],['353','354'])).

thf('356',plain,(
    sk_C_1 = sk_F_2 ),
    inference(demod,[status(thm)],['319','355'])).

thf('357',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('358',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('359',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('360',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('361',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('362',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('363',plain,
    ( ( ( k2_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
      = sk_B_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['361','362'])).

thf('364',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('365',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('366',plain,
    ( ( ( k2_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
      = sk_B_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['363','364','365'])).

thf('367',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
      = sk_B_1 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['360','366'])).

thf('368',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('369',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B_1 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['367','368'])).

thf('370',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('371',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('372',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B_1 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 ) )
      = sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['369','370','371'])).

thf('373',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('374',plain,
    ( ( sk_B_1 = sk_E_2 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B_1 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['372','373'])).

thf('375',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('376',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( sk_E_2 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_B_1 )
      | ( sk_F_2 = k1_xboole_0 )
      | ( sk_B_1 = sk_E_2 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_E_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('378',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( sk_E_2 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_B_1 )
      | ( sk_F_2 = k1_xboole_0 )
      | ( sk_B_1 = sk_E_2 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_E_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['376','377'])).

thf('379',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E_2 @ X0 )
      | ( sk_B_1 = sk_E_2 )
      | ( sk_F_2 = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_B_1 )
      | ( sk_E_2 = k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['378'])).

thf('380',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['85'])).

thf('381',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B_1 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,
    ( ( sk_B_1 = sk_E_2 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B_1 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['381'])).

thf('383',plain,
    ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','106'])).

thf('384',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('385',plain,
    ( ( ( k2_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['383','384'])).

thf('386',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('387',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('388',plain,
    ( ( k2_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['385','386','387'])).

thf('389',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('390',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('391',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) )
        = X1 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['389','390'])).

thf('392',plain,
    ( ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D_1 @ sk_E_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['388','391'])).

thf('393',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) )
        = X36 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('394',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E_2 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['392','393'])).

thf('395',plain,
    ( ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E_2 ) ),
    inference(simplify,[status(thm)],['394'])).

thf('396',plain,
    ( ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 )
    | ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 ) ),
    inference('sup+',[status(thm)],['382','395'])).

thf('397',plain,
    ( ( sk_F_2 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 ) ),
    inference(simplify,[status(thm)],['396'])).

thf('398',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('399',plain,
    ( ( v1_xboole_0 @ sk_F_2 )
    | ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['397','398'])).

thf('400',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F_2 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('401',plain,
    ( ( sk_E_2 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['399','400'])).

thf('402',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('403',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['401','402'])).

thf('404',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('405',plain,
    ( ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_E_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['403','404'])).

thf('406',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('407',plain,
    ( ( v1_xboole_0 @ sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 ) ),
    inference('sup+',[status(thm)],['405','406'])).

thf('408',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ sk_E_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','185'])).

thf('409',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = sk_E_2 )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_F_2 ) ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 )
      | ( sk_B_1 = sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['359','409'])).

thf('411',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('412',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2 ) )
      | ( sk_D_1 = k1_xboole_0 )
      | ( sk_B_1 = sk_E_2 ) ) ),
    inference(demod,[status(thm)],['410','411'])).

thf('413',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2 ) )
    | ( sk_B_1 = sk_E_2 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['358','412'])).

thf('414',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 ) ),
    inference('sup-',[status(thm)],['357','413'])).

thf('415',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('416',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 ) ),
    inference(demod,[status(thm)],['414','415'])).

thf('417',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['215','230','231','232'])).

thf('418',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B_1 = sk_E_2 ) ) ),
    inference('sup+',[status(thm)],['416','417'])).

thf('419',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2 ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('420',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = sk_E_2 ) ),
    inference('sup-',[status(thm)],['418','419'])).

thf('421',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('422',plain,(
    sk_B_1 = sk_E_2 ),
    inference(demod,[status(thm)],['420','421'])).

thf('423',plain,
    ( ( sk_B_1 != sk_E_2 )
   <= ( sk_B_1 != sk_E_2 ) ),
    inference(split,[status(esa)],['241'])).

thf('424',plain,
    ( ( sk_E_2 != sk_E_2 )
   <= ( sk_B_1 != sk_E_2 ) ),
    inference('sup-',[status(thm)],['422','423'])).

thf('425',plain,(
    sk_B_1 = sk_E_2 ),
    inference(simplify,[status(thm)],['424'])).

thf('426',plain,
    ( ( sk_A != sk_D_1 )
    | ( sk_B_1 != sk_E_2 )
    | ( sk_C_1 != sk_F_2 ) ),
    inference(split,[status(esa)],['241'])).

thf('427',plain,(
    sk_A != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['356','425','426'])).

thf('428',plain,(
    sk_A != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['242','427'])).

thf('429',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['240','428'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2C10whxGKu
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:11:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 47.14/47.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 47.14/47.37  % Solved by: fo/fo7.sh
% 47.14/47.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.14/47.37  % done 34450 iterations in 46.909s
% 47.14/47.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 47.14/47.37  % SZS output start Refutation
% 47.14/47.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 47.14/47.37  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 47.14/47.37  thf(sk_A_type, type, sk_A: $i).
% 47.14/47.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 47.14/47.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 47.14/47.37  thf(sk_B_type, type, sk_B: $i > $i).
% 47.14/47.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 47.14/47.37  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 47.14/47.37  thf(sk_C_1_type, type, sk_C_1: $i).
% 47.14/47.37  thf(sk_B_1_type, type, sk_B_1: $i).
% 47.14/47.37  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 47.14/47.37  thf(sk_F_2_type, type, sk_F_2: $i).
% 47.14/47.37  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 47.14/47.37  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 47.14/47.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 47.14/47.37  thf(sk_D_1_type, type, sk_D_1: $i).
% 47.14/47.37  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 47.14/47.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 47.14/47.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.14/47.37  thf(sk_E_2_type, type, sk_E_2: $i).
% 47.14/47.37  thf(d1_xboole_0, axiom,
% 47.14/47.37    (![A:$i]:
% 47.14/47.37     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 47.14/47.37  thf('0', plain,
% 47.14/47.37      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 47.14/47.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 47.14/47.37  thf(d2_zfmisc_1, axiom,
% 47.14/47.37    (![A:$i,B:$i,C:$i]:
% 47.14/47.37     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 47.14/47.37       ( ![D:$i]:
% 47.14/47.37         ( ( r2_hidden @ D @ C ) <=>
% 47.14/47.37           ( ?[E:$i,F:$i]:
% 47.14/47.37             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 47.14/47.37               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 47.14/47.37  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 47.14/47.37  thf(zf_stmt_1, axiom,
% 47.14/47.37    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 47.14/47.37     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 47.14/47.37       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 47.14/47.37         ( r2_hidden @ E @ A ) ) ))).
% 47.14/47.37  thf(zf_stmt_2, axiom,
% 47.14/47.37    (![A:$i,B:$i,C:$i]:
% 47.14/47.37     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 47.14/47.37       ( ![D:$i]:
% 47.14/47.37         ( ( r2_hidden @ D @ C ) <=>
% 47.14/47.37           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 47.14/47.37  thf('1', plain,
% 47.14/47.37      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 47.14/47.37         (~ (r2_hidden @ X22 @ X21)
% 47.14/47.37          | (zip_tseitin_0 @ (sk_F_1 @ X22 @ X19 @ X20) @ 
% 47.14/47.37             (sk_E_1 @ X22 @ X19 @ X20) @ X22 @ X19 @ X20)
% 47.14/47.37          | ((X21) != (k2_zfmisc_1 @ X20 @ X19)))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 47.14/47.37  thf('2', plain,
% 47.14/47.37      (![X19 : $i, X20 : $i, X22 : $i]:
% 47.14/47.37         ((zip_tseitin_0 @ (sk_F_1 @ X22 @ X19 @ X20) @ 
% 47.14/47.37           (sk_E_1 @ X22 @ X19 @ X20) @ X22 @ X19 @ X20)
% 47.14/47.37          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X20 @ X19)))),
% 47.14/47.37      inference('simplify', [status(thm)], ['1'])).
% 47.14/47.37  thf('3', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 47.14/47.37          | (zip_tseitin_0 @ 
% 47.14/47.37             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 47.14/47.37             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 47.14/47.37             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['0', '2'])).
% 47.14/47.37  thf('4', plain,
% 47.14/47.37      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.14/47.37         ((r2_hidden @ X10 @ X14)
% 47.14/47.37          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 47.14/47.37  thf('5', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1))
% 47.14/47.37          | (r2_hidden @ 
% 47.14/47.37             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['3', '4'])).
% 47.14/47.37  thf('6', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 47.14/47.37  thf('7', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['5', '6'])).
% 47.14/47.37  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 47.14/47.37  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf(fc3_zfmisc_1, axiom,
% 47.14/47.37    (![A:$i,B:$i]:
% 47.14/47.37     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 47.14/47.37  thf('9', plain,
% 47.14/47.37      (![X26 : $i, X27 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X26 @ X27)) | ~ (v1_xboole_0 @ X27))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 47.14/47.37  thf(d3_tarski, axiom,
% 47.14/47.37    (![A:$i,B:$i]:
% 47.14/47.37     ( ( r1_tarski @ A @ B ) <=>
% 47.14/47.37       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 47.14/47.37  thf('10', plain,
% 47.14/47.37      (![X4 : $i, X6 : $i]:
% 47.14/47.37         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_tarski])).
% 47.14/47.37  thf('11', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 47.14/47.37  thf('12', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['10', '11'])).
% 47.14/47.37  thf(t135_zfmisc_1, axiom,
% 47.14/47.37    (![A:$i,B:$i]:
% 47.14/47.37     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 47.14/47.37         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 47.14/47.37       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 47.14/47.37  thf('13', plain,
% 47.14/47.37      (![X31 : $i, X32 : $i]:
% 47.14/47.37         (((X31) = (k1_xboole_0))
% 47.14/47.37          | ~ (r1_tarski @ X31 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 47.14/47.37  thf('14', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('15', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['9', '14'])).
% 47.14/47.37  thf(d3_zfmisc_1, axiom,
% 47.14/47.37    (![A:$i,B:$i,C:$i]:
% 47.14/47.37     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 47.14/47.37       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 47.14/47.37  thf('16', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('17', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['15', '16'])).
% 47.14/47.37  thf('18', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['8', '17'])).
% 47.14/47.37  thf('19', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['8', '17'])).
% 47.14/47.37  thf('20', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('21', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('22', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 47.14/47.37      inference('sup+', [status(thm)], ['20', '21'])).
% 47.14/47.37  thf('23', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         ((k1_xboole_0)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ k1_xboole_0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['19', '22'])).
% 47.14/47.37  thf('24', plain,
% 47.14/47.37      (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['18', '23'])).
% 47.14/47.37  thf('25', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('26', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['24', '25'])).
% 47.14/47.37  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('28', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['9', '14'])).
% 47.14/47.37  thf('29', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('30', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['28', '29'])).
% 47.14/47.37  thf('31', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('32', plain,
% 47.14/47.37      (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['18', '23'])).
% 47.14/47.37  thf('33', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['31', '32'])).
% 47.14/47.37  thf('34', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('35', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 47.14/47.37            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['33', '34'])).
% 47.14/47.37  thf('36', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X3 @ k1_xboole_0 @ X0) = (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X1)
% 47.14/47.37          | ~ (v1_xboole_0 @ X3))),
% 47.14/47.37      inference('sup+', [status(thm)], ['30', '35'])).
% 47.14/47.37  thf('37', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ X0)
% 47.14/47.37          | ((k3_zfmisc_1 @ X0 @ k1_xboole_0 @ X1)
% 47.14/47.37              = (k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['27', '36'])).
% 47.14/47.37  thf('38', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37            = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['26', '37'])).
% 47.14/47.37  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('40', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('41', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('42', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf(t195_relat_1, axiom,
% 47.14/47.37    (![A:$i,B:$i]:
% 47.14/47.37     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 47.14/47.37          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 47.14/47.37               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 47.14/47.37  thf('43', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('44', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37            = (k2_zfmisc_1 @ X2 @ X1))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['42', '43'])).
% 47.14/47.37  thf(t36_mcart_1, conjecture,
% 47.14/47.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 47.14/47.37     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 47.14/47.37       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 47.14/47.37         ( ( C ) = ( k1_xboole_0 ) ) | 
% 47.14/47.37         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 47.14/47.37  thf(zf_stmt_3, negated_conjecture,
% 47.14/47.37    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 47.14/47.37        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 47.14/47.37          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 47.14/47.37            ( ( C ) = ( k1_xboole_0 ) ) | 
% 47.14/47.37            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 47.14/47.37    inference('cnf.neg', [status(esa)], [t36_mcart_1])).
% 47.14/47.37  thf('45', plain,
% 47.14/47.37      (((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 47.14/47.37         = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('46', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37            = (k2_zfmisc_1 @ X2 @ X1))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['42', '43'])).
% 47.14/47.37  thf('47', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['45', '46'])).
% 47.14/47.37  thf('48', plain, (((sk_C_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('49', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 47.14/47.37  thf('50', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('51', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.37          = (sk_A))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['49', '50'])).
% 47.14/47.37  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('53', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('54', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.37          = (sk_A))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['51', '52', '53'])).
% 47.14/47.37  thf('55', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) = (sk_A))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['44', '54'])).
% 47.14/47.37  thf('56', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('57', plain,
% 47.14/47.37      ((((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) = (sk_A))
% 47.14/47.37        | ((sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['55', '56'])).
% 47.14/47.37  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('59', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('60', plain,
% 47.14/47.37      ((((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) = (sk_A)))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['57', '58', '59'])).
% 47.14/47.37  thf('61', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('62', plain,
% 47.14/47.37      ((((sk_A) = (sk_D_1))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['60', '61'])).
% 47.14/47.37  thf('63', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['10', '11'])).
% 47.14/47.37  thf(t117_zfmisc_1, axiom,
% 47.14/47.37    (![A:$i,B:$i,C:$i]:
% 47.14/47.37     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 47.14/47.37          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 47.14/47.37            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 47.14/47.37          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 47.14/47.37  thf('64', plain,
% 47.14/47.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 47.14/47.37         (((X28) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ X29 @ X30)
% 47.14/47.37          | ~ (r1_tarski @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 47.14/47.37               (k2_zfmisc_1 @ X28 @ X30)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 47.14/47.37  thf('65', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2))
% 47.14/47.37          | (r1_tarski @ X2 @ X0)
% 47.14/47.37          | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['63', '64'])).
% 47.14/47.37  thf('66', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37          | ((sk_A) = (sk_D_1))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ sk_E_2 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['62', '65'])).
% 47.14/47.37  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('68', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37          | ((sk_A) = (sk_D_1))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ sk_E_2 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['66', '67'])).
% 47.14/47.37  thf('69', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         ((r1_tarski @ sk_E_2 @ X0)
% 47.14/47.37          | ((sk_A) = (sk_D_1))
% 47.14/47.37          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37          | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('simplify', [status(thm)], ['68'])).
% 47.14/47.37  thf('70', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         ((k1_xboole_0)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ k1_xboole_0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['19', '22'])).
% 47.14/47.37  thf('71', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2))
% 47.14/47.37          | (r1_tarski @ X2 @ X0)
% 47.14/47.37          | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['63', '64'])).
% 47.14/47.37  thf('72', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ k1_xboole_0 @ X3))),
% 47.14/47.37      inference('sup-', [status(thm)], ['70', '71'])).
% 47.14/47.37  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('74', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ k1_xboole_0 @ X3))),
% 47.14/47.37      inference('demod', [status(thm)], ['72', '73'])).
% 47.14/47.37  thf('75', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['24', '25'])).
% 47.14/47.37  thf('76', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | (r1_tarski @ k1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['74', '75'])).
% 47.14/47.37  thf('77', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['10', '11'])).
% 47.14/47.37  thf('78', plain,
% 47.14/47.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 47.14/47.37         (((X28) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ X29 @ X30)
% 47.14/47.37          | ~ (r1_tarski @ (k2_zfmisc_1 @ X29 @ X28) @ 
% 47.14/47.37               (k2_zfmisc_1 @ X30 @ X28)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 47.14/47.37  thf('79', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0))
% 47.14/47.37          | (r1_tarski @ X2 @ X1)
% 47.14/47.37          | ((X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['77', '78'])).
% 47.14/47.37  thf('80', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | (r1_tarski @ k1_xboole_0 @ X2)
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ k1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['76', '79'])).
% 47.14/47.37  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('82', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         ((r1_tarski @ k1_xboole_0 @ X2)
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ k1_xboole_0 @ X1))),
% 47.14/47.37      inference('demod', [status(thm)], ['80', '81'])).
% 47.14/47.37  thf('83', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((r1_tarski @ k1_xboole_0 @ X0) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('condensation', [status(thm)], ['82'])).
% 47.14/47.37  thf(d10_xboole_0, axiom,
% 47.14/47.37    (![A:$i,B:$i]:
% 47.14/47.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 47.14/47.37  thf('84', plain,
% 47.14/47.37      (![X7 : $i, X9 : $i]:
% 47.14/47.37         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 47.14/47.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.14/47.37  thf('85', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (((X1) = (k1_xboole_0))
% 47.14/47.37          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 47.14/47.37          | ((X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['83', '84'])).
% 47.14/47.37  thf('86', plain,
% 47.14/47.37      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 47.14/47.37      inference('condensation', [status(thm)], ['85'])).
% 47.14/47.37  thf('87', plain,
% 47.14/47.37      ((((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['69', '86'])).
% 47.14/47.37  thf('88', plain,
% 47.14/47.37      ((((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('simplify', [status(thm)], ['87'])).
% 47.14/47.37  thf('89', plain,
% 47.14/47.37      (((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 47.14/47.37         = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('90', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37            = (k2_zfmisc_1 @ X2 @ X1))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['42', '43'])).
% 47.14/47.37  thf(fc10_subset_1, axiom,
% 47.14/47.37    (![A:$i,B:$i]:
% 47.14/47.37     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 47.14/47.37       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 47.14/47.37  thf('91', plain,
% 47.14/47.37      (![X33 : $i, X34 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ X33)
% 47.14/47.37          | (v1_xboole_0 @ X34)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc10_subset_1])).
% 47.14/47.37  thf('92', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | ((X2) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k3_zfmisc_1 @ X1 @ X0 @ X2))
% 47.14/47.37              = (k2_zfmisc_1 @ X1 @ X0))
% 47.14/47.37          | (v1_xboole_0 @ X0)
% 47.14/47.37          | (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['90', '91'])).
% 47.14/47.37  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('94', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((X2) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k3_zfmisc_1 @ X1 @ X0 @ X2))
% 47.14/47.37              = (k2_zfmisc_1 @ X1 @ X0))
% 47.14/47.37          | (v1_xboole_0 @ X0)
% 47.14/47.37          | (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('demod', [status(thm)], ['92', '93'])).
% 47.14/47.37  thf('95', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | (v1_xboole_0 @ sk_A)
% 47.14/47.37        | (v1_xboole_0 @ sk_B_1)
% 47.14/47.37        | ((sk_C_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['89', '94'])).
% 47.14/47.37  thf('96', plain, (((sk_C_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('97', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | (v1_xboole_0 @ sk_A)
% 47.14/47.37        | (v1_xboole_0 @ sk_B_1))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 47.14/47.37  thf('98', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('100', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['98', '99'])).
% 47.14/47.37  thf('101', plain, (~ (v1_xboole_0 @ sk_A)),
% 47.14/47.37      inference('simplify', [status(thm)], ['100'])).
% 47.14/47.37  thf('102', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_B_1)
% 47.14/47.37        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37            = (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.14/47.37      inference('clc', [status(thm)], ['97', '101'])).
% 47.14/47.37  thf('103', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('104', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('105', plain, (![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['103', '104'])).
% 47.14/47.37  thf('106', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 47.14/47.37      inference('simplify', [status(thm)], ['105'])).
% 47.14/47.37  thf('107', plain,
% 47.14/47.37      (((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 47.14/47.37      inference('clc', [status(thm)], ['102', '106'])).
% 47.14/47.37  thf('108', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('109', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.37          = (sk_A))
% 47.14/47.37        | ((sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['107', '108'])).
% 47.14/47.37  thf('110', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('111', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('112', plain,
% 47.14/47.37      (((k1_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.37         = (sk_A))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['109', '110', '111'])).
% 47.14/47.37  thf('113', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37            = (k2_zfmisc_1 @ X2 @ X1))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['42', '43'])).
% 47.14/47.37  thf('114', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('115', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k1_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))) = (X2))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((X1) = (k1_xboole_0))
% 47.14/47.37          | ((X2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['113', '114'])).
% 47.14/47.37  thf('116', plain,
% 47.14/47.37      ((((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['112', '115'])).
% 47.14/47.37  thf('117', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X35))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('118', plain,
% 47.14/47.37      ((((k1_relat_1 @ k1_xboole_0) = (sk_D_1))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['116', '117'])).
% 47.14/47.37  thf('119', plain,
% 47.14/47.37      ((((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((k1_relat_1 @ k1_xboole_0) = (sk_D_1)))),
% 47.14/47.37      inference('simplify', [status(thm)], ['118'])).
% 47.14/47.37  thf('120', plain,
% 47.14/47.37      ((((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['88', '119'])).
% 47.14/47.37  thf('121', plain,
% 47.14/47.37      ((((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('simplify', [status(thm)], ['120'])).
% 47.14/47.37  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('123', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_F_2)
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['121', '122'])).
% 47.14/47.37  thf('124', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['15', '16'])).
% 47.14/47.37  thf('125', plain,
% 47.14/47.37      (((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 47.14/47.37         = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('126', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['8', '17'])).
% 47.14/47.37  thf('127', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('128', plain,
% 47.14/47.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 47.14/47.37         (((X28) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ X29 @ X30)
% 47.14/47.37          | ~ (r1_tarski @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 47.14/47.37               (k2_zfmisc_1 @ X28 @ X30)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 47.14/47.37  thf('129', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 47.14/47.37             (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X3))
% 47.14/47.37          | (r1_tarski @ X0 @ X3)
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['127', '128'])).
% 47.14/47.37  thf('130', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('131', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 47.14/47.37             (k3_zfmisc_1 @ X2 @ X1 @ X3))
% 47.14/47.37          | (r1_tarski @ X0 @ X3)
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('demod', [status(thm)], ['129', '130'])).
% 47.14/47.37  thf('132', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ X2) @ k1_xboole_0)
% 47.14/47.37          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 47.14/47.37          | (r1_tarski @ X2 @ k1_xboole_0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['126', '131'])).
% 47.14/47.37  thf('133', plain,
% 47.14/47.37      ((~ (r1_tarski @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2) @ k1_xboole_0)
% 47.14/47.37        | (r1_tarski @ sk_C_1 @ k1_xboole_0)
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['125', '132'])).
% 47.14/47.37  thf('134', plain,
% 47.14/47.37      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 47.14/47.37        | ~ (v1_xboole_0 @ sk_F_2)
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['124', '133'])).
% 47.14/47.37  thf('135', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((r1_tarski @ k1_xboole_0 @ X0) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('condensation', [status(thm)], ['82'])).
% 47.14/47.37  thf('136', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('137', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: (((sk_A) != (X0)) | (r1_tarski @ k1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['135', '136'])).
% 47.14/47.37  thf('138', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 47.14/47.37      inference('simplify', [status(thm)], ['137'])).
% 47.14/47.37  thf('139', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ sk_F_2)
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 47.14/47.37      inference('demod', [status(thm)], ['134', '138'])).
% 47.14/47.37  thf('140', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['15', '16'])).
% 47.14/47.37  thf('141', plain,
% 47.14/47.37      (((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 47.14/47.37         = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('142', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('143', plain,
% 47.14/47.37      (![X31 : $i, X32 : $i]:
% 47.14/47.37         (((X31) = (k1_xboole_0))
% 47.14/47.37          | ~ (r1_tarski @ X31 @ (k2_zfmisc_1 @ X32 @ X31)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 47.14/47.37  thf('144', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (r1_tarski @ X0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37          | ((X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['142', '143'])).
% 47.14/47.37  thf('145', plain,
% 47.14/47.37      ((~ (r1_tarski @ sk_C_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37        | ((sk_C_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['141', '144'])).
% 47.14/47.37  thf('146', plain, (((sk_C_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('147', plain,
% 47.14/47.37      (~ (r1_tarski @ sk_C_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 47.14/47.37  thf('148', plain,
% 47.14/47.37      ((~ (r1_tarski @ sk_C_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_F_2))),
% 47.14/47.37      inference('sup-', [status(thm)], ['140', '147'])).
% 47.14/47.37  thf('149', plain,
% 47.14/47.37      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ~ (v1_xboole_0 @ sk_F_2))),
% 47.14/47.37      inference('clc', [status(thm)], ['139', '148'])).
% 47.14/47.37  thf('150', plain,
% 47.14/47.37      (((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 47.14/47.37      inference('clc', [status(thm)], ['102', '106'])).
% 47.14/47.37  thf('151', plain,
% 47.14/47.37      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37          = (k1_xboole_0))
% 47.14/47.37        | ~ (v1_xboole_0 @ sk_F_2))),
% 47.14/47.37      inference('demod', [status(thm)], ['149', '150'])).
% 47.14/47.37  thf('152', plain,
% 47.14/47.37      ((((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37            = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['123', '151'])).
% 47.14/47.37  thf('153', plain,
% 47.14/47.37      (((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 47.14/47.37      inference('clc', [status(thm)], ['102', '106'])).
% 47.14/47.37  thf('154', plain,
% 47.14/47.37      (![X33 : $i, X34 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ X33)
% 47.14/47.37          | (v1_xboole_0 @ X34)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc10_subset_1])).
% 47.14/47.37  thf('155', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ 
% 47.14/47.37           (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.37        | (v1_xboole_0 @ sk_B_1)
% 47.14/47.37        | (v1_xboole_0 @ sk_A))),
% 47.14/47.37      inference('sup-', [status(thm)], ['153', '154'])).
% 47.14/47.37  thf('156', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 47.14/47.37      inference('simplify', [status(thm)], ['105'])).
% 47.14/47.37  thf('157', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_A)
% 47.14/47.37        | ~ (v1_xboole_0 @ 
% 47.14/47.37             (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))))),
% 47.14/47.37      inference('clc', [status(thm)], ['155', '156'])).
% 47.14/47.37  thf('158', plain, (~ (v1_xboole_0 @ sk_A)),
% 47.14/47.37      inference('simplify', [status(thm)], ['100'])).
% 47.14/47.37  thf('159', plain,
% 47.14/47.37      (~ (v1_xboole_0 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 47.14/47.37      inference('clc', [status(thm)], ['157', '158'])).
% 47.14/47.37  thf('160', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['152', '159'])).
% 47.14/47.37  thf('161', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('162', plain,
% 47.14/47.37      ((((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('demod', [status(thm)], ['160', '161'])).
% 47.14/47.37  thf('163', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('164', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_E_2)
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['162', '163'])).
% 47.14/47.37  thf('165', plain,
% 47.14/47.37      (![X26 : $i, X27 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X26 @ X27)) | ~ (v1_xboole_0 @ X27))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 47.14/47.37  thf('166', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('167', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('168', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['166', '167'])).
% 47.14/47.37  thf('169', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ X0)
% 47.14/47.37          | ~ (v1_xboole_0 @ X2)
% 47.14/47.37          | ((X2) = (k2_zfmisc_1 @ X1 @ X0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['165', '168'])).
% 47.14/47.37  thf('170', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('171', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k2_zfmisc_1 @ X0 @ X1))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0)
% 47.14/47.37          | ~ (v1_xboole_0 @ X2))),
% 47.14/47.37      inference('sup+', [status(thm)], ['169', '170'])).
% 47.14/47.37  thf('172', plain,
% 47.14/47.37      (((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 47.14/47.37         = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('173', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('174', plain,
% 47.14/47.37      (![X33 : $i, X34 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ X33)
% 47.14/47.37          | (v1_xboole_0 @ X34)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc10_subset_1])).
% 47.14/47.37  thf('175', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37          | (v1_xboole_0 @ X0)
% 47.14/47.37          | (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['173', '174'])).
% 47.14/47.37  thf('176', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | (v1_xboole_0 @ sk_C_1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['172', '175'])).
% 47.14/47.37  thf('177', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('178', plain, (((sk_C_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('179', plain, (![X0 : $i]: (((sk_C_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['177', '178'])).
% 47.14/47.37  thf('180', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 47.14/47.37      inference('simplify', [status(thm)], ['179'])).
% 47.14/47.37  thf('181', plain,
% 47.14/47.37      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 47.14/47.37      inference('clc', [status(thm)], ['176', '180'])).
% 47.14/47.37  thf('182', plain,
% 47.14/47.37      (((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.37         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 47.14/47.37      inference('clc', [status(thm)], ['102', '106'])).
% 47.14/47.37  thf('183', plain,
% 47.14/47.37      (((v1_xboole_0 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.37        | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 47.14/47.37      inference('demod', [status(thm)], ['181', '182'])).
% 47.14/47.37  thf('184', plain,
% 47.14/47.37      (~ (v1_xboole_0 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 47.14/47.37      inference('clc', [status(thm)], ['157', '158'])).
% 47.14/47.37  thf('185', plain,
% 47.14/47.37      (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('clc', [status(thm)], ['183', '184'])).
% 47.14/47.37  thf('186', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_F_2))
% 47.14/47.37          | ~ (v1_xboole_0 @ sk_E_2)
% 47.14/47.37          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['171', '185'])).
% 47.14/47.37  thf('187', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (((sk_A) = (sk_D_1))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_F_2)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['164', '186'])).
% 47.14/47.37  thf('188', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37          | ~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['41', '187'])).
% 47.14/47.37  thf('189', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('190', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('demod', [status(thm)], ['188', '189'])).
% 47.14/47.37  thf('191', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37        | ((sk_A) = (sk_D_1))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['40', '190'])).
% 47.14/47.37  thf('192', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['7', '191'])).
% 47.14/47.37  thf('193', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('194', plain, ((((sk_D_1) = (k1_xboole_0)) | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('demod', [status(thm)], ['192', '193'])).
% 47.14/47.37  thf('195', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('196', plain, (((v1_xboole_0 @ sk_D_1) | ((sk_A) = (sk_D_1)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['194', '195'])).
% 47.14/47.37  thf('197', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['10', '11'])).
% 47.14/47.37  thf('198', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('199', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('200', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k2_zfmisc_1 @ X0 @ X1) = (k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['198', '199'])).
% 47.14/47.37  thf('201', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('202', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('203', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X2)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) @ X2))),
% 47.14/47.37      inference('sup+', [status(thm)], ['201', '202'])).
% 47.14/47.37  thf('204', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X2)
% 47.14/47.37            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))
% 47.14/47.37          | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['200', '203'])).
% 47.14/47.37  thf('205', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('206', plain,
% 47.14/47.37      (![X31 : $i, X32 : $i]:
% 47.14/47.37         (((X31) = (k1_xboole_0))
% 47.14/47.37          | ~ (r1_tarski @ X31 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 47.14/47.37  thf('207', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['205', '206'])).
% 47.14/47.37  thf('208', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 47.14/47.37             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1) @ X0 @ X2))
% 47.14/47.37          | ~ (v1_xboole_0 @ X3)
% 47.14/47.37          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1) @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['204', '207'])).
% 47.14/47.37  thf('209', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 47.14/47.37      inference('sup+', [status(thm)], ['20', '21'])).
% 47.14/47.37  thf('210', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('211', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 47.14/47.37             (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X1 @ X0) @ X2))
% 47.14/47.37          | ~ (v1_xboole_0 @ X3)
% 47.14/47.37          | ((k3_zfmisc_1 @ X3 @ X1 @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('demod', [status(thm)], ['208', '209', '210'])).
% 47.14/47.37  thf('212', plain,
% 47.14/47.37      (![X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X1))
% 47.14/47.37          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X3))),
% 47.14/47.37      inference('sup-', [status(thm)], ['197', '211'])).
% 47.14/47.37  thf('213', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k2_zfmisc_1 @ X0 @ X1) = (k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['198', '199'])).
% 47.14/47.37  thf('214', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X2)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) @ X2))),
% 47.14/47.37      inference('sup+', [status(thm)], ['201', '202'])).
% 47.14/47.37  thf('215', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X0)
% 47.14/47.37            = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ k1_xboole_0 @ X2)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['213', '214'])).
% 47.14/47.37  thf('216', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['5', '6'])).
% 47.14/47.37  thf('217', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['10', '11'])).
% 47.14/47.37  thf('218', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('219', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['9', '14'])).
% 47.14/47.37  thf('220', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 47.14/47.37           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 47.14/47.37      inference('sup+', [status(thm)], ['20', '21'])).
% 47.14/47.37  thf('221', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 47.14/47.37            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X2))),
% 47.14/47.37      inference('sup+', [status(thm)], ['219', '220'])).
% 47.14/47.37  thf('222', plain,
% 47.14/47.37      (![X31 : $i, X32 : $i]:
% 47.14/47.37         (((X31) = (k1_xboole_0))
% 47.14/47.37          | ~ (r1_tarski @ X31 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 47.14/47.37  thf('223', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ 
% 47.14/47.37             (k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X2)
% 47.14/47.37          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['221', '222'])).
% 47.14/47.37  thf('224', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ 
% 47.14/47.37             (k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1))
% 47.14/47.37          | ((k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 47.14/47.37          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['218', '223'])).
% 47.14/47.37  thf('225', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('226', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ 
% 47.14/47.37             (k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1))
% 47.14/47.37          | ((k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('demod', [status(thm)], ['224', '225'])).
% 47.14/47.37  thf('227', plain,
% 47.14/47.37      (![X1 : $i, X2 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1))
% 47.14/47.37          | ((k3_zfmisc_1 @ X2 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['217', '226'])).
% 47.14/47.37  thf('228', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['216', '227'])).
% 47.14/47.37  thf('229', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('230', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 47.14/47.37      inference('demod', [status(thm)], ['228', '229'])).
% 47.14/47.37  thf('231', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 47.14/47.37      inference('demod', [status(thm)], ['228', '229'])).
% 47.14/47.37  thf('232', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('233', plain,
% 47.14/47.37      (![X0 : $i, X2 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X0) = (k1_xboole_0))),
% 47.14/47.37      inference('demod', [status(thm)], ['215', '230', '231', '232'])).
% 47.14/47.37  thf('234', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('235', plain,
% 47.14/47.37      (![X1 : $i, X2 : $i, X3 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 47.14/47.37      inference('demod', [status(thm)], ['212', '233', '234'])).
% 47.14/47.37  thf('236', plain,
% 47.14/47.37      (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('clc', [status(thm)], ['183', '184'])).
% 47.14/47.37  thf('237', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_D_1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['235', '236'])).
% 47.14/47.37  thf('238', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('239', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 47.14/47.37      inference('demod', [status(thm)], ['237', '238'])).
% 47.14/47.37  thf('240', plain, (((sk_A) = (sk_D_1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['196', '239'])).
% 47.14/47.37  thf('241', plain,
% 47.14/47.37      ((((sk_A) != (sk_D_1)) | ((sk_B_1) != (sk_E_2)) | ((sk_C_1) != (sk_F_2)))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('242', plain, ((((sk_A) != (sk_D_1))) <= (~ (((sk_A) = (sk_D_1))))),
% 47.14/47.37      inference('split', [status(esa)], ['241'])).
% 47.14/47.37  thf('243', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['5', '6'])).
% 47.14/47.37  thf('244', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('245', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('246', plain,
% 47.14/47.37      (((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 47.14/47.37         = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('247', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('248', plain,
% 47.14/47.37      (![X35 : $i, X36 : $i]:
% 47.14/47.37         (((X35) = (k1_xboole_0))
% 47.14/47.37          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.37          | ((X36) = (k1_xboole_0)))),
% 47.14/47.37      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.37  thf('249', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['247', '248'])).
% 47.14/47.37  thf('250', plain,
% 47.14/47.37      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)) = (sk_C_1))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['246', '249'])).
% 47.14/47.37  thf('251', plain, (((sk_C_1) != (k1_xboole_0))),
% 47.14/47.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.37  thf('252', plain,
% 47.14/47.37      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)) = (sk_C_1))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('simplify_reflect-', [status(thm)], ['250', '251'])).
% 47.14/47.37  thf('253', plain,
% 47.14/47.37      (![X33 : $i, X34 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ X33)
% 47.14/47.37          | (v1_xboole_0 @ X34)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc10_subset_1])).
% 47.14/47.37  thf('254', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37        | ((k2_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)) = (sk_C_1))
% 47.14/47.37        | (v1_xboole_0 @ sk_B_1)
% 47.14/47.37        | (v1_xboole_0 @ sk_A))),
% 47.14/47.37      inference('sup-', [status(thm)], ['252', '253'])).
% 47.14/47.37  thf('255', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('256', plain,
% 47.14/47.37      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)) = (sk_C_1))
% 47.14/47.37        | (v1_xboole_0 @ sk_B_1)
% 47.14/47.37        | (v1_xboole_0 @ sk_A))),
% 47.14/47.37      inference('demod', [status(thm)], ['254', '255'])).
% 47.14/47.37  thf('257', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 47.14/47.37      inference('simplify', [status(thm)], ['105'])).
% 47.14/47.37  thf('258', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_A)
% 47.14/47.37        | ((k2_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)) = (sk_C_1)))),
% 47.14/47.37      inference('clc', [status(thm)], ['256', '257'])).
% 47.14/47.37  thf('259', plain, (~ (v1_xboole_0 @ sk_A)),
% 47.14/47.37      inference('simplify', [status(thm)], ['100'])).
% 47.14/47.37  thf('260', plain,
% 47.14/47.37      (((k2_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)) = (sk_C_1))),
% 47.14/47.37      inference('clc', [status(thm)], ['258', '259'])).
% 47.14/47.37  thf('261', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 47.14/47.37          | ((X0) = (k1_xboole_0))
% 47.14/47.37          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['247', '248'])).
% 47.14/47.37  thf('262', plain,
% 47.14/47.37      ((((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['260', '261'])).
% 47.14/47.37  thf('263', plain,
% 47.14/47.37      (![X33 : $i, X34 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ X33)
% 47.14/47.37          | (v1_xboole_0 @ X34)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc10_subset_1])).
% 47.14/47.37  thf('264', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | (v1_xboole_0 @ sk_E_2)
% 47.14/47.37        | (v1_xboole_0 @ sk_D_1))),
% 47.14/47.37      inference('sup-', [status(thm)], ['262', '263'])).
% 47.14/47.37  thf('265', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('266', plain,
% 47.14/47.37      ((((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | (v1_xboole_0 @ sk_E_2)
% 47.14/47.37        | (v1_xboole_0 @ sk_D_1))),
% 47.14/47.37      inference('demod', [status(thm)], ['264', '265'])).
% 47.14/47.37  thf('267', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('268', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_D_1)
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['266', '267'])).
% 47.14/47.37  thf('269', plain,
% 47.14/47.37      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.37  thf('270', plain,
% 47.14/47.37      ((((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['268', '269'])).
% 47.14/47.37  thf('271', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('272', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_F_2)
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['270', '271'])).
% 47.14/47.37  thf('273', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('274', plain,
% 47.14/47.37      (![X26 : $i, X27 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X26 @ X27)) | ~ (v1_xboole_0 @ X27))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 47.14/47.37  thf('275', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup+', [status(thm)], ['273', '274'])).
% 47.14/47.37  thf('276', plain,
% 47.14/47.37      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.37        | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 47.14/47.37      inference('clc', [status(thm)], ['176', '180'])).
% 47.14/47.37  thf('277', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ sk_F_2)
% 47.14/47.37        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['275', '276'])).
% 47.14/47.37  thf('278', plain,
% 47.14/47.37      ((((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['272', '277'])).
% 47.14/47.37  thf('279', plain,
% 47.14/47.37      (![X33 : $i, X34 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ X33)
% 47.14/47.37          | (v1_xboole_0 @ X34)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 47.14/47.37      inference('cnf', [status(esa)], [fc10_subset_1])).
% 47.14/47.37  thf('280', plain,
% 47.14/47.37      ((((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | (v1_xboole_0 @ sk_B_1)
% 47.14/47.37        | (v1_xboole_0 @ sk_A))),
% 47.14/47.37      inference('sup-', [status(thm)], ['278', '279'])).
% 47.14/47.37  thf('281', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 47.14/47.37      inference('simplify', [status(thm)], ['105'])).
% 47.14/47.37  thf('282', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_A)
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['280', '281'])).
% 47.14/47.37  thf('283', plain, (~ (v1_xboole_0 @ sk_A)),
% 47.14/47.37      inference('simplify', [status(thm)], ['100'])).
% 47.14/47.37  thf('284', plain,
% 47.14/47.37      ((((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['282', '283'])).
% 47.14/47.37  thf('285', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('286', plain,
% 47.14/47.37      (((v1_xboole_0 @ sk_E_2)
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['284', '285'])).
% 47.14/47.37  thf('287', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_F_2))
% 47.14/47.37          | ~ (v1_xboole_0 @ sk_E_2)
% 47.14/47.37          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['171', '185'])).
% 47.14/47.37  thf('288', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (((sk_D_1) = (k1_xboole_0))
% 47.14/47.37          | ((sk_C_1) = (sk_F_2))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0)
% 47.14/47.37          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_F_2)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['286', '287'])).
% 47.14/47.37  thf('289', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37          | ~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37          | ((sk_C_1) = (sk_F_2))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['245', '288'])).
% 47.14/47.37  thf('290', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('291', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37          | ((sk_C_1) = (sk_F_2))
% 47.14/47.37          | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('demod', [status(thm)], ['289', '290'])).
% 47.14/47.37  thf('292', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['244', '291'])).
% 47.14/47.37  thf('293', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['243', '292'])).
% 47.14/47.37  thf('294', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.37  thf('295', plain, ((((sk_C_1) = (sk_F_2)) | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.37      inference('demod', [status(thm)], ['293', '294'])).
% 47.14/47.37  thf('296', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.37      inference('sup-', [status(thm)], ['5', '6'])).
% 47.14/47.37  thf('297', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.37           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.37      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.37  thf('298', plain,
% 47.14/47.37      ((((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['260', '261'])).
% 47.14/47.37  thf('299', plain,
% 47.14/47.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 47.14/47.37         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 47.14/47.37           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 47.14/47.37      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.14/47.37  thf('300', plain,
% 47.14/47.37      (![X0 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ X0)
% 47.14/47.37            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37          | ((sk_C_1) = (sk_F_2)))),
% 47.14/47.37      inference('sup+', [status(thm)], ['298', '299'])).
% 47.14/47.37  thf('301', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['28', '29'])).
% 47.14/47.37  thf('302', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.37         (((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ X0))
% 47.14/47.37          | ((sk_C_1) = (sk_F_2))
% 47.14/47.37          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37          | ~ (v1_xboole_0 @ X1))),
% 47.14/47.37      inference('sup+', [status(thm)], ['300', '301'])).
% 47.14/47.37  thf('303', plain,
% 47.14/47.37      (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.37      inference('clc', [status(thm)], ['183', '184'])).
% 47.14/47.37  thf('304', plain,
% 47.14/47.37      (![X0 : $i, X1 : $i]:
% 47.14/47.37         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ sk_F_2))
% 47.14/47.37          | ~ (v1_xboole_0 @ X0)
% 47.14/47.37          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.37          | ((sk_C_1) = (sk_F_2)))),
% 47.14/47.37      inference('sup-', [status(thm)], ['302', '303'])).
% 47.14/47.37  thf('305', plain,
% 47.14/47.37      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.37        | ((sk_C_1) = (sk_F_2))
% 47.14/47.37        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 47.14/47.38      inference('sup-', [status(thm)], ['297', '304'])).
% 47.14/47.38  thf('306', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('307', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.38        | ((sk_C_1) = (sk_F_2))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('demod', [status(thm)], ['305', '306'])).
% 47.14/47.38  thf('308', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_C_1) = (sk_F_2)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['296', '307'])).
% 47.14/47.38  thf('309', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('310', plain, ((((sk_F_2) = (k1_xboole_0)) | ((sk_C_1) = (sk_F_2)))),
% 47.14/47.38      inference('demod', [status(thm)], ['308', '309'])).
% 47.14/47.38  thf('311', plain,
% 47.14/47.38      ((((sk_F_2) = (sk_D_1)) | ((sk_C_1) = (sk_F_2)) | ((sk_C_1) = (sk_F_2)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['295', '310'])).
% 47.14/47.38  thf('312', plain, ((((sk_C_1) = (sk_F_2)) | ((sk_F_2) = (sk_D_1)))),
% 47.14/47.38      inference('simplify', [status(thm)], ['311'])).
% 47.14/47.38  thf('313', plain, ((((sk_C_1) != (sk_F_2))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('split', [status(esa)], ['241'])).
% 47.14/47.38  thf('314', plain,
% 47.14/47.38      (((((sk_F_2) != (sk_F_2)) | ((sk_F_2) = (sk_D_1))))
% 47.14/47.38         <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('sup-', [status(thm)], ['312', '313'])).
% 47.14/47.38  thf('315', plain, ((((sk_F_2) = (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify', [status(thm)], ['314'])).
% 47.14/47.38  thf('316', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.38      inference('sup+', [status(thm)], ['273', '274'])).
% 47.14/47.38  thf('317', plain,
% 47.14/47.38      (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.38      inference('clc', [status(thm)], ['183', '184'])).
% 47.14/47.38  thf('318', plain, (~ (v1_xboole_0 @ sk_F_2)),
% 47.14/47.38      inference('sup-', [status(thm)], ['316', '317'])).
% 47.14/47.38  thf('319', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ sk_D_1)) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('sup-', [status(thm)], ['315', '318'])).
% 47.14/47.38  thf('320', plain, ((((sk_C_1) = (sk_F_2)) | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('demod', [status(thm)], ['293', '294'])).
% 47.14/47.38  thf('321', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('322', plain,
% 47.14/47.38      ((((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_C_1) = (sk_F_2))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['282', '283'])).
% 47.14/47.38  thf('323', plain,
% 47.14/47.38      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ((X1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['12', '13'])).
% 47.14/47.38  thf('324', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (((X0) = (sk_E_2))
% 47.14/47.38          | ((sk_C_1) = (sk_F_2))
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.38      inference('sup+', [status(thm)], ['322', '323'])).
% 47.14/47.38  thf('325', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('326', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ sk_D_1)
% 47.14/47.38          | ~ (v1_xboole_0 @ X0)
% 47.14/47.38          | ((sk_C_1) = (sk_F_2))
% 47.14/47.38          | ((X0) = (sk_E_2)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['324', '325'])).
% 47.14/47.38  thf('327', plain,
% 47.14/47.38      ((((k1_xboole_0) = (sk_E_2))
% 47.14/47.38        | ((sk_C_1) = (sk_F_2))
% 47.14/47.38        | (v1_xboole_0 @ sk_D_1))),
% 47.14/47.38      inference('sup-', [status(thm)], ['321', '326'])).
% 47.14/47.38  thf('328', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ sk_D_1)) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('sup-', [status(thm)], ['315', '318'])).
% 47.14/47.38  thf('329', plain,
% 47.14/47.38      (((((sk_C_1) = (sk_F_2)) | ((k1_xboole_0) = (sk_E_2))))
% 47.14/47.38         <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('sup-', [status(thm)], ['327', '328'])).
% 47.14/47.38  thf('330', plain, ((((sk_F_2) = (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify', [status(thm)], ['314'])).
% 47.14/47.38  thf('331', plain,
% 47.14/47.38      (((((sk_C_1) = (sk_D_1)) | ((k1_xboole_0) = (sk_E_2))))
% 47.14/47.38         <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('demod', [status(thm)], ['329', '330'])).
% 47.14/47.38  thf('332', plain, ((((sk_C_1) != (sk_F_2))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('split', [status(esa)], ['241'])).
% 47.14/47.38  thf('333', plain, ((((sk_F_2) = (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify', [status(thm)], ['314'])).
% 47.14/47.38  thf('334', plain, ((((sk_C_1) != (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('demod', [status(thm)], ['332', '333'])).
% 47.14/47.38  thf('335', plain,
% 47.14/47.38      ((((k1_xboole_0) = (sk_E_2))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['331', '334'])).
% 47.14/47.38  thf('336', plain,
% 47.14/47.38      (((((sk_D_1) = (sk_E_2)) | ((sk_C_1) = (sk_F_2))))
% 47.14/47.38         <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('sup+', [status(thm)], ['320', '335'])).
% 47.14/47.38  thf('337', plain, ((((sk_F_2) = (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify', [status(thm)], ['314'])).
% 47.14/47.38  thf('338', plain,
% 47.14/47.38      (((((sk_D_1) = (sk_E_2)) | ((sk_C_1) = (sk_D_1))))
% 47.14/47.38         <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('demod', [status(thm)], ['336', '337'])).
% 47.14/47.38  thf('339', plain, ((((sk_C_1) != (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('demod', [status(thm)], ['332', '333'])).
% 47.14/47.38  thf('340', plain, ((((sk_D_1) = (sk_E_2))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['338', '339'])).
% 47.14/47.38  thf('341', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('342', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.38      inference('sup+', [status(thm)], ['273', '274'])).
% 47.14/47.38  thf('343', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ sk_D_1)
% 47.14/47.38          | ~ (v1_xboole_0 @ X0)
% 47.14/47.38          | ((sk_C_1) = (sk_F_2))
% 47.14/47.38          | ((X0) = (sk_E_2)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['324', '325'])).
% 47.14/47.38  thf('344', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         (~ (v1_xboole_0 @ X0)
% 47.14/47.38          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (sk_E_2))
% 47.14/47.38          | ((sk_C_1) = (sk_F_2))
% 47.14/47.38          | (v1_xboole_0 @ sk_D_1))),
% 47.14/47.38      inference('sup-', [status(thm)], ['342', '343'])).
% 47.14/47.38  thf('345', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ sk_D_1)
% 47.14/47.38          | ((sk_C_1) = (sk_F_2))
% 47.14/47.38          | ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (sk_E_2)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['341', '344'])).
% 47.14/47.38  thf('346', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.38      inference('sup+', [status(thm)], ['273', '274'])).
% 47.14/47.38  thf('347', plain,
% 47.14/47.38      (((v1_xboole_0 @ sk_E_2)
% 47.14/47.38        | ((sk_C_1) = (sk_F_2))
% 47.14/47.38        | (v1_xboole_0 @ sk_D_1)
% 47.14/47.38        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 47.14/47.38      inference('sup+', [status(thm)], ['345', '346'])).
% 47.14/47.38  thf('348', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('349', plain,
% 47.14/47.38      (((v1_xboole_0 @ sk_E_2) | ((sk_C_1) = (sk_F_2)) | (v1_xboole_0 @ sk_D_1))),
% 47.14/47.38      inference('demod', [status(thm)], ['347', '348'])).
% 47.14/47.38  thf('350', plain,
% 47.14/47.38      ((((v1_xboole_0 @ sk_D_1)
% 47.14/47.38         | (v1_xboole_0 @ sk_D_1)
% 47.14/47.38         | ((sk_C_1) = (sk_F_2)))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('sup+', [status(thm)], ['340', '349'])).
% 47.14/47.38  thf('351', plain, ((((sk_F_2) = (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify', [status(thm)], ['314'])).
% 47.14/47.38  thf('352', plain,
% 47.14/47.38      ((((v1_xboole_0 @ sk_D_1)
% 47.14/47.38         | (v1_xboole_0 @ sk_D_1)
% 47.14/47.38         | ((sk_C_1) = (sk_D_1)))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('demod', [status(thm)], ['350', '351'])).
% 47.14/47.38  thf('353', plain,
% 47.14/47.38      (((((sk_C_1) = (sk_D_1)) | (v1_xboole_0 @ sk_D_1)))
% 47.14/47.38         <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify', [status(thm)], ['352'])).
% 47.14/47.38  thf('354', plain, ((((sk_C_1) != (sk_D_1))) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('demod', [status(thm)], ['332', '333'])).
% 47.14/47.38  thf('355', plain, (((v1_xboole_0 @ sk_D_1)) <= (~ (((sk_C_1) = (sk_F_2))))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['353', '354'])).
% 47.14/47.38  thf('356', plain, ((((sk_C_1) = (sk_F_2)))),
% 47.14/47.38      inference('demod', [status(thm)], ['319', '355'])).
% 47.14/47.38  thf('357', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i]:
% 47.14/47.38         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 47.14/47.38      inference('sup-', [status(thm)], ['5', '6'])).
% 47.14/47.38  thf('358', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i]:
% 47.14/47.38         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.38           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.38      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.38  thf('359', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i]:
% 47.14/47.38         ((k2_zfmisc_1 @ k1_xboole_0 @ X0)
% 47.14/47.38           = (k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0))),
% 47.14/47.38      inference('demod', [status(thm)], ['38', '39'])).
% 47.14/47.38  thf('360', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.38            = (k2_zfmisc_1 @ X2 @ X1))
% 47.14/47.38          | ((X0) = (k1_xboole_0))
% 47.14/47.38          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['42', '43'])).
% 47.14/47.38  thf('361', plain,
% 47.14/47.38      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.38          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 47.14/47.38  thf('362', plain,
% 47.14/47.38      (![X35 : $i, X36 : $i]:
% 47.14/47.38         (((X35) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.38          | ((X36) = (k1_xboole_0)))),
% 47.14/47.38      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.38  thf('363', plain,
% 47.14/47.38      ((((k2_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.38          = (sk_B_1))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_A) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['361', '362'])).
% 47.14/47.38  thf('364', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.38  thf('365', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.38  thf('366', plain,
% 47.14/47.38      ((((k2_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.38          = (sk_B_1))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['363', '364', '365'])).
% 47.14/47.38  thf('367', plain,
% 47.14/47.38      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) = (sk_B_1))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['360', '366'])).
% 47.14/47.38  thf('368', plain,
% 47.14/47.38      (![X35 : $i, X36 : $i]:
% 47.14/47.38         (((X35) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.38          | ((X36) = (k1_xboole_0)))),
% 47.14/47.38      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.38  thf('369', plain,
% 47.14/47.38      ((((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) = (sk_B_1))
% 47.14/47.38        | ((sk_B_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_A) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['367', '368'])).
% 47.14/47.38  thf('370', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.38  thf('371', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.38  thf('372', plain,
% 47.14/47.38      ((((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_2)) = (sk_B_1)))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['369', '370', '371'])).
% 47.14/47.38  thf('373', plain,
% 47.14/47.38      (![X35 : $i, X36 : $i]:
% 47.14/47.38         (((X35) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.38          | ((X36) = (k1_xboole_0)))),
% 47.14/47.38      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.38  thf('374', plain,
% 47.14/47.38      ((((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['372', '373'])).
% 47.14/47.38  thf('375', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2))
% 47.14/47.38          | (r1_tarski @ X2 @ X0)
% 47.14/47.38          | ((X1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['63', '64'])).
% 47.14/47.38  thf('376', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38          | ((sk_B_1) = (sk_E_2))
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | (r1_tarski @ sk_E_2 @ X0))),
% 47.14/47.38      inference('sup-', [status(thm)], ['374', '375'])).
% 47.14/47.38  thf('377', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('378', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38          | ((sk_B_1) = (sk_E_2))
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | (r1_tarski @ sk_E_2 @ X0))),
% 47.14/47.38      inference('demod', [status(thm)], ['376', '377'])).
% 47.14/47.38  thf('379', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         ((r1_tarski @ sk_E_2 @ X0)
% 47.14/47.38          | ((sk_B_1) = (sk_E_2))
% 47.14/47.38          | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38          | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('simplify', [status(thm)], ['378'])).
% 47.14/47.38  thf('380', plain,
% 47.14/47.38      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 47.14/47.38      inference('condensation', [status(thm)], ['85'])).
% 47.14/47.38  thf('381', plain,
% 47.14/47.38      ((((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['379', '380'])).
% 47.14/47.38  thf('382', plain,
% 47.14/47.38      ((((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_relat_1 @ k1_xboole_0) = (sk_B_1))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('simplify', [status(thm)], ['381'])).
% 47.14/47.38  thf('383', plain,
% 47.14/47.38      (((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.38         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 47.14/47.38      inference('clc', [status(thm)], ['102', '106'])).
% 47.14/47.38  thf('384', plain,
% 47.14/47.38      (![X35 : $i, X36 : $i]:
% 47.14/47.38         (((X35) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.38          | ((X36) = (k1_xboole_0)))),
% 47.14/47.38      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.38  thf('385', plain,
% 47.14/47.38      ((((k2_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.38          = (sk_B_1))
% 47.14/47.38        | ((sk_B_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_A) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['383', '384'])).
% 47.14/47.38  thf('386', plain, (((sk_A) != (k1_xboole_0))),
% 47.14/47.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.38  thf('387', plain, (((sk_B_1) != (k1_xboole_0))),
% 47.14/47.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 47.14/47.38  thf('388', plain,
% 47.14/47.38      (((k2_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))
% 47.14/47.38         = (sk_B_1))),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['385', '386', '387'])).
% 47.14/47.38  thf('389', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.14/47.38            = (k2_zfmisc_1 @ X2 @ X1))
% 47.14/47.38          | ((X0) = (k1_xboole_0))
% 47.14/47.38          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['42', '43'])).
% 47.14/47.38  thf('390', plain,
% 47.14/47.38      (![X35 : $i, X36 : $i]:
% 47.14/47.38         (((X35) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.38          | ((X36) = (k1_xboole_0)))),
% 47.14/47.38      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.38  thf('391', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.14/47.38         (((k2_relat_1 @ (k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))) = (X1))
% 47.14/47.38          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 47.14/47.38          | ((X0) = (k1_xboole_0))
% 47.14/47.38          | ((X1) = (k1_xboole_0))
% 47.14/47.38          | ((X2) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['389', '390'])).
% 47.14/47.38  thf('392', plain,
% 47.14/47.38      ((((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_zfmisc_1 @ sk_D_1 @ sk_E_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['388', '391'])).
% 47.14/47.38  thf('393', plain,
% 47.14/47.38      (![X35 : $i, X36 : $i]:
% 47.14/47.38         (((X35) = (k1_xboole_0))
% 47.14/47.38          | ((k2_relat_1 @ (k2_zfmisc_1 @ X35 @ X36)) = (X36))
% 47.14/47.38          | ((X36) = (k1_xboole_0)))),
% 47.14/47.38      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.14/47.38  thf('394', plain,
% 47.14/47.38      ((((k2_relat_1 @ k1_xboole_0) = (sk_E_2))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['392', '393'])).
% 47.14/47.38  thf('395', plain,
% 47.14/47.38      ((((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((k2_relat_1 @ k1_xboole_0) = (sk_E_2)))),
% 47.14/47.38      inference('simplify', [status(thm)], ['394'])).
% 47.14/47.38  thf('396', plain,
% 47.14/47.38      ((((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['382', '395'])).
% 47.14/47.38  thf('397', plain,
% 47.14/47.38      ((((sk_F_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('simplify', [status(thm)], ['396'])).
% 47.14/47.38  thf('398', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('399', plain,
% 47.14/47.38      (((v1_xboole_0 @ sk_F_2)
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['397', '398'])).
% 47.14/47.38  thf('400', plain,
% 47.14/47.38      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.38          = (k1_xboole_0))
% 47.14/47.38        | ~ (v1_xboole_0 @ sk_F_2))),
% 47.14/47.38      inference('demod', [status(thm)], ['149', '150'])).
% 47.14/47.38  thf('401', plain,
% 47.14/47.38      ((((sk_E_2) = (k1_xboole_0))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))
% 47.14/47.38            = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['399', '400'])).
% 47.14/47.38  thf('402', plain,
% 47.14/47.38      (~ (v1_xboole_0 @ (k1_relat_1 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2)))),
% 47.14/47.38      inference('clc', [status(thm)], ['157', '158'])).
% 47.14/47.38  thf('403', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['401', '402'])).
% 47.14/47.38  thf('404', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('405', plain,
% 47.14/47.38      ((((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_E_2) = (k1_xboole_0)))),
% 47.14/47.38      inference('demod', [status(thm)], ['403', '404'])).
% 47.14/47.38  thf('406', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('407', plain,
% 47.14/47.38      (((v1_xboole_0 @ sk_E_2)
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['405', '406'])).
% 47.14/47.38  thf('408', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_F_2))
% 47.14/47.38          | ~ (v1_xboole_0 @ sk_E_2)
% 47.14/47.38          | ~ (v1_xboole_0 @ X0))),
% 47.14/47.38      inference('sup-', [status(thm)], ['171', '185'])).
% 47.14/47.38  thf('409', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (((sk_B_1) = (sk_E_2))
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | ~ (v1_xboole_0 @ X0)
% 47.14/47.38          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_F_2)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['407', '408'])).
% 47.14/47.38  thf('410', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.38          | ~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['359', '409'])).
% 47.14/47.38  thf('411', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('412', plain,
% 47.14/47.38      (![X0 : $i]:
% 47.14/47.38         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X0 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.38          | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38          | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('demod', [status(thm)], ['410', '411'])).
% 47.14/47.38  thf('413', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_F_2))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2))
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['358', '412'])).
% 47.14/47.38  thf('414', plain,
% 47.14/47.38      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.14/47.38        | ((sk_D_1) = (k1_xboole_0))
% 47.14/47.38        | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['357', '413'])).
% 47.14/47.38  thf('415', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('416', plain, ((((sk_D_1) = (k1_xboole_0)) | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('demod', [status(thm)], ['414', '415'])).
% 47.14/47.38  thf('417', plain,
% 47.14/47.38      (![X0 : $i, X2 : $i]:
% 47.14/47.38         ((k3_zfmisc_1 @ k1_xboole_0 @ X2 @ X0) = (k1_xboole_0))),
% 47.14/47.38      inference('demod', [status(thm)], ['215', '230', '231', '232'])).
% 47.14/47.38  thf('418', plain,
% 47.14/47.38      (![X0 : $i, X1 : $i]:
% 47.14/47.38         (((k3_zfmisc_1 @ sk_D_1 @ X1 @ X0) = (k1_xboole_0))
% 47.14/47.38          | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('sup+', [status(thm)], ['416', '417'])).
% 47.14/47.38  thf('419', plain,
% 47.14/47.38      (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D_1 @ sk_E_2 @ sk_F_2))),
% 47.14/47.38      inference('clc', [status(thm)], ['183', '184'])).
% 47.14/47.38  thf('420', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('sup-', [status(thm)], ['418', '419'])).
% 47.14/47.38  thf('421', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.14/47.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 47.14/47.38  thf('422', plain, (((sk_B_1) = (sk_E_2))),
% 47.14/47.38      inference('demod', [status(thm)], ['420', '421'])).
% 47.14/47.38  thf('423', plain, ((((sk_B_1) != (sk_E_2))) <= (~ (((sk_B_1) = (sk_E_2))))),
% 47.14/47.38      inference('split', [status(esa)], ['241'])).
% 47.14/47.38  thf('424', plain, ((((sk_E_2) != (sk_E_2))) <= (~ (((sk_B_1) = (sk_E_2))))),
% 47.14/47.38      inference('sup-', [status(thm)], ['422', '423'])).
% 47.14/47.38  thf('425', plain, ((((sk_B_1) = (sk_E_2)))),
% 47.14/47.38      inference('simplify', [status(thm)], ['424'])).
% 47.14/47.38  thf('426', plain,
% 47.14/47.38      (~ (((sk_A) = (sk_D_1))) | ~ (((sk_B_1) = (sk_E_2))) | 
% 47.14/47.38       ~ (((sk_C_1) = (sk_F_2)))),
% 47.14/47.38      inference('split', [status(esa)], ['241'])).
% 47.14/47.38  thf('427', plain, (~ (((sk_A) = (sk_D_1)))),
% 47.14/47.38      inference('sat_resolution*', [status(thm)], ['356', '425', '426'])).
% 47.14/47.38  thf('428', plain, (((sk_A) != (sk_D_1))),
% 47.14/47.38      inference('simpl_trail', [status(thm)], ['242', '427'])).
% 47.14/47.38  thf('429', plain, ($false),
% 47.14/47.38      inference('simplify_reflect-', [status(thm)], ['240', '428'])).
% 47.14/47.38  
% 47.14/47.38  % SZS output end Refutation
% 47.14/47.38  
% 47.14/47.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
