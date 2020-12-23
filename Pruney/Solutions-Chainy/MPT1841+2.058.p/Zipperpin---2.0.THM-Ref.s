%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.898fkdXPCq

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:37 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 142 expanded)
%              Number of leaves         :   44 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  721 (1040 expanded)
%              Number of equality atoms :   45 (  48 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X72: $i,X73: $i] :
      ( ( v1_xboole_0 @ X72 )
      | ~ ( m1_subset_1 @ X73 @ X72 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X72 @ X73 ) @ ( k1_zfmisc_1 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X74: $i,X75: $i] :
      ( ( v1_xboole_0 @ X74 )
      | ~ ( m1_subset_1 @ X75 @ X74 )
      | ( ( k6_domain_1 @ X74 @ X75 )
        = ( k1_tarski @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ X77 ) )
      | ~ ( v1_subset_1 @ X76 @ X77 )
      | ( v1_xboole_0 @ X76 )
      | ~ ( v1_zfmisc_1 @ X77 )
      | ( v1_xboole_0 @ X77 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X60: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X61: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('23',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( r2_hidden @ X67 @ X68 )
      | ~ ( v1_xboole_0 @ X69 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k6_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
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

thf('43',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 )
      | ( r2_hidden @ X48 @ X57 )
      | ( X57
       != ( k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X48 @ ( k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49 ) )
      | ( zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X39 != X38 )
      | ~ ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X38: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ~ ( zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','25'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.898fkdXPCq
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:24:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.21/3.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.21/3.43  % Solved by: fo/fo7.sh
% 3.21/3.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.43  % done 1497 iterations in 2.961s
% 3.21/3.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.21/3.43  % SZS output start Refutation
% 3.21/3.43  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.21/3.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.21/3.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.21/3.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.21/3.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.21/3.43  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 3.21/3.43  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 3.21/3.43  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.21/3.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.21/3.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.21/3.43  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 3.21/3.43  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 3.21/3.43  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 3.21/3.43  thf(sk_B_type, type, sk_B: $i > $i).
% 3.21/3.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.21/3.43  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 3.21/3.43  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 3.21/3.43  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 3.21/3.43                                               $i > $i > $i > $o).
% 3.21/3.43  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.21/3.43  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 3.21/3.43                                           $i > $i).
% 3.21/3.43  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.21/3.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.21/3.43  thf(t6_tex_2, conjecture,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.21/3.43       ( ![B:$i]:
% 3.21/3.43         ( ( m1_subset_1 @ B @ A ) =>
% 3.21/3.43           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 3.21/3.43                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 3.21/3.43  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.43    (~( ![A:$i]:
% 3.21/3.43        ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.21/3.43          ( ![B:$i]:
% 3.21/3.43            ( ( m1_subset_1 @ B @ A ) =>
% 3.21/3.43              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 3.21/3.43                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 3.21/3.43    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 3.21/3.43  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(dt_k6_domain_1, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 3.21/3.43       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.21/3.43  thf('1', plain,
% 3.21/3.43      (![X72 : $i, X73 : $i]:
% 3.21/3.43         ((v1_xboole_0 @ X72)
% 3.21/3.43          | ~ (m1_subset_1 @ X73 @ X72)
% 3.21/3.43          | (m1_subset_1 @ (k6_domain_1 @ X72 @ X73) @ (k1_zfmisc_1 @ X72)))),
% 3.21/3.43      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 3.21/3.43  thf('2', plain,
% 3.21/3.43      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 3.21/3.43        | (v1_xboole_0 @ sk_A))),
% 3.21/3.43      inference('sup-', [status(thm)], ['0', '1'])).
% 3.21/3.43  thf('3', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(redefinition_k6_domain_1, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 3.21/3.43       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 3.21/3.43  thf('4', plain,
% 3.21/3.43      (![X74 : $i, X75 : $i]:
% 3.21/3.43         ((v1_xboole_0 @ X74)
% 3.21/3.43          | ~ (m1_subset_1 @ X75 @ X74)
% 3.21/3.43          | ((k6_domain_1 @ X74 @ X75) = (k1_tarski @ X75)))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 3.21/3.43  thf('5', plain,
% 3.21/3.43      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 3.21/3.43        | (v1_xboole_0 @ sk_A))),
% 3.21/3.43      inference('sup-', [status(thm)], ['3', '4'])).
% 3.21/3.43  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 3.21/3.43      inference('clc', [status(thm)], ['5', '6'])).
% 3.21/3.43  thf('8', plain,
% 3.21/3.43      (((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 3.21/3.43        | (v1_xboole_0 @ sk_A))),
% 3.21/3.43      inference('demod', [status(thm)], ['2', '7'])).
% 3.21/3.43  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('10', plain,
% 3.21/3.43      ((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 3.21/3.43      inference('clc', [status(thm)], ['8', '9'])).
% 3.21/3.43  thf(cc2_tex_2, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 3.21/3.43       ( ![B:$i]:
% 3.21/3.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.21/3.43           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 3.21/3.43  thf('11', plain,
% 3.21/3.43      (![X76 : $i, X77 : $i]:
% 3.21/3.43         (~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ X77))
% 3.21/3.43          | ~ (v1_subset_1 @ X76 @ X77)
% 3.21/3.43          | (v1_xboole_0 @ X76)
% 3.21/3.43          | ~ (v1_zfmisc_1 @ X77)
% 3.21/3.43          | (v1_xboole_0 @ X77))),
% 3.21/3.43      inference('cnf', [status(esa)], [cc2_tex_2])).
% 3.21/3.43  thf('12', plain,
% 3.21/3.43      (((v1_xboole_0 @ sk_A)
% 3.21/3.43        | ~ (v1_zfmisc_1 @ sk_A)
% 3.21/3.43        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 3.21/3.43        | ~ (v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A))),
% 3.21/3.43      inference('sup-', [status(thm)], ['10', '11'])).
% 3.21/3.43  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 3.21/3.43      inference('clc', [status(thm)], ['5', '6'])).
% 3.21/3.43  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 3.21/3.43      inference('demod', [status(thm)], ['14', '15'])).
% 3.21/3.43  thf('17', plain,
% 3.21/3.43      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 3.21/3.43      inference('demod', [status(thm)], ['12', '13', '16'])).
% 3.21/3.43  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_2))),
% 3.21/3.43      inference('clc', [status(thm)], ['17', '18'])).
% 3.21/3.43  thf(rc2_subset_1, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ?[B:$i]:
% 3.21/3.43       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 3.21/3.43  thf('20', plain, (![X60 : $i]: (v1_xboole_0 @ (sk_B_1 @ X60))),
% 3.21/3.43      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.21/3.43  thf(d1_xboole_0, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.21/3.43  thf('21', plain,
% 3.21/3.43      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.21/3.43      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.21/3.43  thf(t4_subset_1, axiom,
% 3.21/3.43    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.21/3.43  thf('22', plain,
% 3.21/3.43      (![X61 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 3.21/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.21/3.43  thf(t5_subset, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.21/3.43          ( v1_xboole_0 @ C ) ) ))).
% 3.21/3.43  thf('23', plain,
% 3.21/3.43      (![X67 : $i, X68 : $i, X69 : $i]:
% 3.21/3.43         (~ (r2_hidden @ X67 @ X68)
% 3.21/3.43          | ~ (v1_xboole_0 @ X69)
% 3.21/3.43          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X69)))),
% 3.21/3.43      inference('cnf', [status(esa)], [t5_subset])).
% 3.21/3.43  thf('24', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['22', '23'])).
% 3.21/3.43  thf('25', plain,
% 3.21/3.43      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['21', '24'])).
% 3.21/3.43  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('sup-', [status(thm)], ['20', '25'])).
% 3.21/3.43  thf(d3_tarski, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( r1_tarski @ A @ B ) <=>
% 3.21/3.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.21/3.43  thf('27', plain,
% 3.21/3.43      (![X4 : $i, X6 : $i]:
% 3.21/3.43         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.21/3.43      inference('cnf', [status(esa)], [d3_tarski])).
% 3.21/3.43  thf('28', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.21/3.43      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.21/3.43  thf('29', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['27', '28'])).
% 3.21/3.43  thf('30', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['27', '28'])).
% 3.21/3.43  thf(d10_xboole_0, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.21/3.43  thf('31', plain,
% 3.21/3.43      (![X7 : $i, X9 : $i]:
% 3.21/3.43         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.21/3.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.43  thf('32', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.21/3.43      inference('sup-', [status(thm)], ['30', '31'])).
% 3.21/3.43  thf('33', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['29', '32'])).
% 3.21/3.43  thf('34', plain,
% 3.21/3.43      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.21/3.43      inference('sup-', [status(thm)], ['26', '33'])).
% 3.21/3.43  thf('35', plain, (((k1_xboole_0) = (k1_tarski @ sk_B_2))),
% 3.21/3.43      inference('sup-', [status(thm)], ['19', '34'])).
% 3.21/3.43  thf(t69_enumset1, axiom,
% 3.21/3.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.21/3.43  thf('36', plain,
% 3.21/3.43      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 3.21/3.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.43  thf(t70_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.21/3.43  thf('37', plain,
% 3.21/3.43      (![X11 : $i, X12 : $i]:
% 3.21/3.43         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 3.21/3.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.21/3.43  thf(t71_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.21/3.43  thf('38', plain,
% 3.21/3.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.21/3.43         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 3.21/3.43           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 3.21/3.43      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.21/3.43  thf(t72_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.43     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 3.21/3.43  thf('39', plain,
% 3.21/3.43      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.21/3.43         ((k3_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19)
% 3.21/3.43           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 3.21/3.43      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.21/3.43  thf(t73_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.21/3.43     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 3.21/3.43       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 3.21/3.43  thf('40', plain,
% 3.21/3.43      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.21/3.43         ((k4_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24)
% 3.21/3.43           = (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 3.21/3.43      inference('cnf', [status(esa)], [t73_enumset1])).
% 3.21/3.43  thf(t74_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.21/3.43     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 3.21/3.43       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 3.21/3.43  thf('41', plain,
% 3.21/3.43      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.21/3.43         ((k5_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 3.21/3.43           = (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 3.21/3.43      inference('cnf', [status(esa)], [t74_enumset1])).
% 3.21/3.43  thf(t75_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 3.21/3.43     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 3.21/3.43       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 3.21/3.43  thf('42', plain,
% 3.21/3.43      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.21/3.43         ((k6_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 3.21/3.43           = (k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 3.21/3.43      inference('cnf', [status(esa)], [t75_enumset1])).
% 3.21/3.43  thf(d6_enumset1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 3.21/3.43     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 3.21/3.43       ( ![J:$i]:
% 3.21/3.43         ( ( r2_hidden @ J @ I ) <=>
% 3.21/3.43           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 3.21/3.43                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 3.21/3.43                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 3.21/3.43  thf(zf_stmt_1, type, zip_tseitin_0 :
% 3.21/3.43      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 3.21/3.43  thf(zf_stmt_2, axiom,
% 3.21/3.43    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 3.21/3.43     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 3.21/3.43       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 3.21/3.43         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 3.21/3.43         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 3.21/3.43  thf(zf_stmt_3, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 3.21/3.43     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 3.21/3.43       ( ![J:$i]:
% 3.21/3.43         ( ( r2_hidden @ J @ I ) <=>
% 3.21/3.43           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 3.21/3.43  thf('43', plain,
% 3.21/3.43      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 3.21/3.43         X55 : $i, X56 : $i, X57 : $i]:
% 3.21/3.43         ((zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56)
% 3.21/3.43          | (r2_hidden @ X48 @ X57)
% 3.21/3.43          | ((X57)
% 3.21/3.43              != (k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.21/3.43  thf('44', plain,
% 3.21/3.43      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, 
% 3.21/3.43         X55 : $i, X56 : $i]:
% 3.21/3.43         ((r2_hidden @ X48 @ 
% 3.21/3.43           (k6_enumset1 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 @ X49))
% 3.21/3.43          | (zip_tseitin_0 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ 
% 3.21/3.43             X56))),
% 3.21/3.43      inference('simplify', [status(thm)], ['43'])).
% 3.21/3.43  thf('45', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.21/3.43         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 3.21/3.43          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 3.21/3.43      inference('sup+', [status(thm)], ['42', '44'])).
% 3.21/3.43  thf('46', plain,
% 3.21/3.43      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 3.21/3.43         X45 : $i, X46 : $i]:
% 3.21/3.43         (((X39) != (X38))
% 3.21/3.43          | ~ (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ 
% 3.21/3.43               X38))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.21/3.43  thf('47', plain,
% 3.21/3.43      (![X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 3.21/3.43         X46 : $i]:
% 3.21/3.43         ~ (zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X38)),
% 3.21/3.43      inference('simplify', [status(thm)], ['46'])).
% 3.21/3.43  thf('48', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.21/3.43         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 3.21/3.43      inference('sup-', [status(thm)], ['45', '47'])).
% 3.21/3.43  thf('49', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.21/3.43         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['41', '48'])).
% 3.21/3.43  thf('50', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.21/3.43         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['40', '49'])).
% 3.21/3.43  thf('51', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.43         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['39', '50'])).
% 3.21/3.43  thf('52', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.21/3.43      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.21/3.43  thf('53', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.43         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['51', '52'])).
% 3.21/3.43  thf('54', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.43         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['38', '53'])).
% 3.21/3.43  thf('55', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['37', '54'])).
% 3.21/3.43  thf('56', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['36', '55'])).
% 3.21/3.43  thf('57', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('sup-', [status(thm)], ['35', '56'])).
% 3.21/3.43  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('sup-', [status(thm)], ['20', '25'])).
% 3.21/3.43  thf('59', plain, ($false), inference('demod', [status(thm)], ['57', '58'])).
% 3.21/3.43  
% 3.21/3.43  % SZS output end Refutation
% 3.21/3.43  
% 3.21/3.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
