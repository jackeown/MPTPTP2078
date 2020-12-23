%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E1eKUHz5oZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 142 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  814 (1107 expanded)
%              Number of equality atoms :   62 (  93 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) ) @ ( k1_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('13',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X33 @ X30 @ X31 ) @ ( sk_E_1 @ X33 @ X30 @ X31 ) @ X33 @ X30 @ X31 )
      | ( X32
       != ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X33 @ X30 @ X31 ) @ ( sk_E_1 @ X33 @ X30 @ X31 ) @ X33 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X21 @ X25 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('27',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X37 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','29','30'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('32',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('36',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('37',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('38',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X49 @ X48 ) ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ X24 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['51','56','57'])).

thf('59',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('60',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('65',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E1eKUHz5oZ
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 162 iterations in 0.079s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(cc1_relat_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.53  thf('0', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.53  thf(dt_k5_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.53       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X43 : $i, X44 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X43)
% 0.21/0.53          | ~ (v1_relat_1 @ X44)
% 0.21/0.53          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.53  thf('2', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.53  thf(t60_relat_1, axiom,
% 0.21/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.53  thf(t44_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( r1_tarski @
% 0.21/0.53             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X46 : $i, X47 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X46)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X47 @ X46)) @ 
% 0.21/0.53             (k1_relat_1 @ X47))
% 0.21/0.53          | ~ (v1_relat_1 @ X47))),
% 0.21/0.53      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.53           k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.53             k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.53  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.21/0.53             k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('9', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.53  thf(t22_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k3_xboole_0 @
% 0.21/0.53           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.21/0.53         ( A ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X45 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X45 @ 
% 0.21/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 0.21/0.53            X45))
% 0.21/0.53          | ~ (v1_relat_1 @ X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.53            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.53             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.53            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.53              (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.53               (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.53              = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.53            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.53             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.53            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.53              (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.53               (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.53              = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '16'])).
% 0.21/0.53  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.53              (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.21/0.53               (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.21/0.53              = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf(t7_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf(d2_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ?[E:$i,F:$i]:
% 0.21/0.53             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.53               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_1, axiom,
% 0.21/0.53    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.53       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.53         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X33 @ X32)
% 0.21/0.53          | (zip_tseitin_0 @ (sk_F_1 @ X33 @ X30 @ X31) @ 
% 0.21/0.53             (sk_E_1 @ X33 @ X30 @ X31) @ X33 @ X30 @ X31)
% 0.21/0.53          | ((X32) != (k2_zfmisc_1 @ X31 @ X30)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i, X33 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ (sk_F_1 @ X33 @ X30 @ X31) @ 
% 0.21/0.54           (sk_E_1 @ X33 @ X30 @ X31) @ X33 @ X30 @ X31)
% 0.21/0.54          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X31 @ X30)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | (zip_tseitin_0 @ 
% 0.21/0.54             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.54             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.54             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         ((r2_hidden @ X21 @ X25)
% 0.21/0.54          | ~ (zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.54          | (r2_hidden @ 
% 0.21/0.54             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.54  thf('26', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.54  thf(t55_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.54         (~ (r1_xboole_0 @ (k2_tarski @ X37 @ X38) @ X39)
% 0.21/0.54          | ~ (r2_hidden @ X37 @ X39))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.54  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.54  thf(t2_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '29', '30'])).
% 0.21/0.54  thf(t62_relat_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ A ) =>
% 0.21/0.54          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.21/0.54        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('34', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X43 : $i, X44 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X43)
% 0.21/0.54          | ~ (v1_relat_1 @ X44)
% 0.21/0.54          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.54  thf('36', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.54  thf('37', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf(t45_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ B ) =>
% 0.21/0.54           ( r1_tarski @
% 0.21/0.54             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X48 : $i, X49 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X48)
% 0.21/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X49 @ X48)) @ 
% 0.21/0.54             (k2_relat_1 @ X48))
% 0.21/0.54          | ~ (v1_relat_1 @ X49))),
% 0.21/0.54      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54           k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54             k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.54  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54             k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X45 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X45 @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))) = (
% 0.21/0.54            X45))
% 0.21/0.54          | ~ (v1_relat_1 @ X45))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54             k1_xboole_0))
% 0.21/0.54            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54               k1_xboole_0))
% 0.21/0.54              = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54             k1_xboole_0))
% 0.21/0.54            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54               k1_xboole_0))
% 0.21/0.54              = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '48'])).
% 0.21/0.54  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.54              (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.21/0.54               k1_xboole_0))
% 0.21/0.54              = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | (zip_tseitin_0 @ 
% 0.21/0.54             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.54             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.54             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         ((r2_hidden @ X22 @ X24)
% 0.21/0.54          | ~ (zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.54          | (r2_hidden @ 
% 0.21/0.54             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['51', '56', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.54       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('65', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain, (((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['33', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '66'])).
% 0.21/0.54  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('69', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
