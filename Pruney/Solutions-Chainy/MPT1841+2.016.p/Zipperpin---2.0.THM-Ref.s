%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8cnnVyCTqm

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:31 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 121 expanded)
%              Number of leaves         :   40 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  672 ( 919 expanded)
%              Number of equality atoms :   44 (  49 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X63: $i,X64: $i] :
      ( ( v1_xboole_0 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ X63 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X63 @ X64 ) @ ( k1_zfmisc_1 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X65: $i,X66: $i] :
      ( ( v1_xboole_0 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ X65 )
      | ( ( k6_domain_1 @ X65 @ X66 )
        = ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( v1_subset_1 @ X67 @ X68 )
      | ( v1_xboole_0 @ X67 )
      | ~ ( v1_zfmisc_1 @ X68 )
      | ( v1_xboole_0 @ X68 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X3 @ X3 @ X4 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X5 @ X6 @ X7 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X8 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k5_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X52: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k6_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      | ( r2_hidden @ X40 @ X49 )
      | ( X49
       != ( k6_enumset1 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X40 @ ( k6_enumset1 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 ) )
      | ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X31 != X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X30: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ~ ( zip_tseitin_0 @ X30 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X30 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( r1_tarski @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( v1_xboole_0 @ ( k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8cnnVyCTqm
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.04/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.25  % Solved by: fo/fo7.sh
% 1.04/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.25  % done 831 iterations in 0.790s
% 1.04/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.25  % SZS output start Refutation
% 1.04/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.04/1.25  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.04/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.04/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.04/1.25                                               $i > $i > $i > $o).
% 1.04/1.25  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.04/1.25  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.04/1.25  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.04/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.04/1.25  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.04/1.25  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.04/1.25  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.04/1.25                                           $i > $i).
% 1.04/1.25  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.04/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.25  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.04/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.04/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.25  thf(t6_tex_2, conjecture,
% 1.04/1.25    (![A:$i]:
% 1.04/1.25     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.04/1.25       ( ![B:$i]:
% 1.04/1.25         ( ( m1_subset_1 @ B @ A ) =>
% 1.04/1.25           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 1.04/1.25                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 1.04/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.25    (~( ![A:$i]:
% 1.04/1.25        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.04/1.25          ( ![B:$i]:
% 1.04/1.25            ( ( m1_subset_1 @ B @ A ) =>
% 1.04/1.25              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 1.04/1.25                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 1.04/1.25    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 1.04/1.25  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf(dt_k6_domain_1, axiom,
% 1.04/1.25    (![A:$i,B:$i]:
% 1.04/1.25     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.04/1.25       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.04/1.25  thf('1', plain,
% 1.04/1.25      (![X63 : $i, X64 : $i]:
% 1.04/1.25         ((v1_xboole_0 @ X63)
% 1.04/1.25          | ~ (m1_subset_1 @ X64 @ X63)
% 1.04/1.25          | (m1_subset_1 @ (k6_domain_1 @ X63 @ X64) @ (k1_zfmisc_1 @ X63)))),
% 1.04/1.25      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.04/1.25  thf('2', plain,
% 1.04/1.25      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 1.04/1.25        | (v1_xboole_0 @ sk_A))),
% 1.04/1.25      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.25  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf(redefinition_k6_domain_1, axiom,
% 1.04/1.25    (![A:$i,B:$i]:
% 1.04/1.25     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.04/1.25       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.04/1.25  thf('4', plain,
% 1.04/1.25      (![X65 : $i, X66 : $i]:
% 1.04/1.25         ((v1_xboole_0 @ X65)
% 1.04/1.25          | ~ (m1_subset_1 @ X66 @ X65)
% 1.04/1.25          | ((k6_domain_1 @ X65 @ X66) = (k1_tarski @ X66)))),
% 1.04/1.25      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.04/1.25  thf('5', plain,
% 1.04/1.25      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 1.04/1.25        | (v1_xboole_0 @ sk_A))),
% 1.04/1.25      inference('sup-', [status(thm)], ['3', '4'])).
% 1.04/1.25  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 1.04/1.25      inference('clc', [status(thm)], ['5', '6'])).
% 1.04/1.25  thf('8', plain,
% 1.04/1.25      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 1.04/1.25        | (v1_xboole_0 @ sk_A))),
% 1.04/1.25      inference('demod', [status(thm)], ['2', '7'])).
% 1.04/1.25  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.25      inference('clc', [status(thm)], ['8', '9'])).
% 1.04/1.25  thf(cc2_tex_2, axiom,
% 1.04/1.25    (![A:$i]:
% 1.04/1.25     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.04/1.25       ( ![B:$i]:
% 1.04/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.25           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 1.04/1.25  thf('11', plain,
% 1.04/1.25      (![X67 : $i, X68 : $i]:
% 1.04/1.25         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 1.04/1.25          | ~ (v1_subset_1 @ X67 @ X68)
% 1.04/1.25          | (v1_xboole_0 @ X67)
% 1.04/1.25          | ~ (v1_zfmisc_1 @ X68)
% 1.04/1.25          | (v1_xboole_0 @ X68))),
% 1.04/1.25      inference('cnf', [status(esa)], [cc2_tex_2])).
% 1.04/1.25  thf('12', plain,
% 1.04/1.25      (((v1_xboole_0 @ sk_A)
% 1.04/1.25        | ~ (v1_zfmisc_1 @ sk_A)
% 1.04/1.25        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 1.04/1.25        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 1.04/1.25      inference('sup-', [status(thm)], ['10', '11'])).
% 1.04/1.25  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 1.04/1.25      inference('clc', [status(thm)], ['5', '6'])).
% 1.04/1.25  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 1.04/1.25      inference('demod', [status(thm)], ['14', '15'])).
% 1.04/1.25  thf('17', plain,
% 1.04/1.25      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 1.04/1.25      inference('demod', [status(thm)], ['12', '13', '16'])).
% 1.04/1.25  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 1.04/1.25      inference('clc', [status(thm)], ['17', '18'])).
% 1.04/1.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.04/1.25  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.04/1.25  thf(t8_boole, axiom,
% 1.04/1.25    (![A:$i,B:$i]:
% 1.04/1.25     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.04/1.25  thf('21', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]:
% 1.04/1.25         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.04/1.25      inference('cnf', [status(esa)], [t8_boole])).
% 1.04/1.25  thf('22', plain,
% 1.04/1.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['20', '21'])).
% 1.04/1.25  thf('23', plain, (((k1_xboole_0) = (k1_tarski @ sk_B))),
% 1.04/1.25      inference('sup-', [status(thm)], ['19', '22'])).
% 1.04/1.25  thf(t69_enumset1, axiom,
% 1.04/1.25    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.04/1.25  thf('24', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 1.04/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.04/1.25  thf(t70_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.04/1.25  thf('25', plain,
% 1.04/1.25      (![X3 : $i, X4 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X3 @ X3 @ X4) = (k2_tarski @ X3 @ X4))),
% 1.04/1.25      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.04/1.25  thf(t71_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i]:
% 1.04/1.25     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.04/1.25  thf('26', plain,
% 1.04/1.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.04/1.25         ((k2_enumset1 @ X5 @ X5 @ X6 @ X7) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 1.04/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.04/1.25  thf(t72_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.25     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.04/1.25  thf('27', plain,
% 1.04/1.25      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X8 @ X8 @ X9 @ X10 @ X11)
% 1.04/1.25           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 1.04/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.04/1.25  thf(t73_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.25     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.04/1.25       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.04/1.25  thf('28', plain,
% 1.04/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 @ X16)
% 1.04/1.25           = (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 1.04/1.25      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.04/1.25  thf(t74_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.04/1.25     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.04/1.25       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.04/1.25  thf('29', plain,
% 1.04/1.25      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.04/1.25         ((k5_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.04/1.25           = (k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 1.04/1.25      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.04/1.25  thf('30', plain,
% 1.04/1.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['20', '21'])).
% 1.04/1.25  thf(t4_subset_1, axiom,
% 1.04/1.25    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.04/1.25  thf('31', plain,
% 1.04/1.25      (![X52 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X52))),
% 1.04/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.04/1.25  thf('32', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]:
% 1.04/1.25         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['30', '31'])).
% 1.04/1.25  thf(t3_subset, axiom,
% 1.04/1.25    (![A:$i,B:$i]:
% 1.04/1.25     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.04/1.25  thf('33', plain,
% 1.04/1.25      (![X55 : $i, X56 : $i]:
% 1.04/1.25         ((r1_tarski @ X55 @ X56) | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56)))),
% 1.04/1.25      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.25  thf('34', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | (r1_tarski @ X1 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['32', '33'])).
% 1.04/1.25  thf(t75_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.04/1.25     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.04/1.25       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.04/1.25  thf('35', plain,
% 1.04/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 1.04/1.25           = (k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 1.04/1.25      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.04/1.25  thf(d6_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.04/1.25     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.04/1.25       ( ![J:$i]:
% 1.04/1.25         ( ( r2_hidden @ J @ I ) <=>
% 1.04/1.25           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 1.04/1.25                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 1.04/1.25                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 1.04/1.25  thf(zf_stmt_1, type, zip_tseitin_0 :
% 1.04/1.25      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.04/1.25  thf(zf_stmt_2, axiom,
% 1.04/1.25    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.04/1.25     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.04/1.25       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 1.04/1.25         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 1.04/1.25         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 1.04/1.25  thf(zf_stmt_3, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.04/1.25     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.04/1.25       ( ![J:$i]:
% 1.04/1.25         ( ( r2_hidden @ J @ I ) <=>
% 1.04/1.25           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.04/1.25  thf('36', plain,
% 1.04/1.25      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 1.04/1.25         X47 : $i, X48 : $i, X49 : $i]:
% 1.04/1.25         ((zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 1.04/1.25          | (r2_hidden @ X40 @ X49)
% 1.04/1.25          | ((X49)
% 1.04/1.25              != (k6_enumset1 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41)))),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.04/1.25  thf('37', plain,
% 1.04/1.25      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 1.04/1.25         X47 : $i, X48 : $i]:
% 1.04/1.25         ((r2_hidden @ X40 @ 
% 1.04/1.25           (k6_enumset1 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41))
% 1.04/1.25          | (zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ 
% 1.04/1.25             X48))),
% 1.04/1.25      inference('simplify', [status(thm)], ['36'])).
% 1.04/1.25  thf('38', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.04/1.25         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.04/1.25          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.04/1.25      inference('sup+', [status(thm)], ['35', '37'])).
% 1.04/1.25  thf('39', plain,
% 1.04/1.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 1.04/1.25         X37 : $i, X38 : $i]:
% 1.04/1.25         (((X31) != (X30))
% 1.04/1.25          | ~ (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ 
% 1.04/1.25               X30))),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.04/1.25  thf('40', plain,
% 1.04/1.25      (![X30 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 1.04/1.25         X38 : $i]:
% 1.04/1.25         ~ (zip_tseitin_0 @ X30 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X30)),
% 1.04/1.25      inference('simplify', [status(thm)], ['39'])).
% 1.04/1.25  thf('41', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.04/1.25         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 1.04/1.25      inference('sup-', [status(thm)], ['38', '40'])).
% 1.04/1.25  thf(t7_ordinal1, axiom,
% 1.04/1.25    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.04/1.25  thf('42', plain,
% 1.04/1.25      (![X61 : $i, X62 : $i]:
% 1.04/1.25         (~ (r2_hidden @ X61 @ X62) | ~ (r1_tarski @ X62 @ X61))),
% 1.04/1.25      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.04/1.25  thf('43', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.04/1.25         ~ (r1_tarski @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)),
% 1.04/1.25      inference('sup-', [status(thm)], ['41', '42'])).
% 1.04/1.25  thf('44', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.04/1.25         ~ (v1_xboole_0 @ (k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1))),
% 1.04/1.25      inference('sup-', [status(thm)], ['34', '43'])).
% 1.04/1.25  thf('45', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['29', '44'])).
% 1.04/1.25  thf('46', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.04/1.25         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['28', '45'])).
% 1.04/1.25  thf('47', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.25         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['27', '46'])).
% 1.04/1.25  thf('48', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['26', '47'])).
% 1.04/1.25  thf('49', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['25', '48'])).
% 1.04/1.25  thf('50', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['24', '49'])).
% 1.04/1.25  thf('51', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.25      inference('sup-', [status(thm)], ['23', '50'])).
% 1.04/1.25  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.04/1.25  thf('53', plain, ($false), inference('demod', [status(thm)], ['51', '52'])).
% 1.04/1.25  
% 1.04/1.25  % SZS output end Refutation
% 1.04/1.25  
% 1.04/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
