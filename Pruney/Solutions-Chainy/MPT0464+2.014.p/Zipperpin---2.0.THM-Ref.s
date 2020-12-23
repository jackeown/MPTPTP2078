%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EoAb1EZK0q

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:10 EST 2020

% Result     : Theorem 10.78s
% Output     : Refutation 10.78s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 185 expanded)
%              Number of leaves         :   38 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  962 (1911 expanded)
%              Number of equality atoms :   42 (  85 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X57 @ X58 ) )
      = ( k3_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k6_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
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

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      | ( r2_hidden @ X45 @ X54 )
      | ( X54
       != ( k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ X45 @ ( k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 ) )
      | ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X36 != X37 )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X35: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ~ ( zip_tseitin_0 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X35 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X62 ) @ X63 )
      | ~ ( r2_hidden @ X63 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('23',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X57 @ X58 ) )
      = ( k3_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','25'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X59: $i,X61: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X61 ) )
      | ~ ( r1_tarski @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X65 ) )
      | ( v1_relat_1 @ X64 )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ~ ( v1_relat_1 @ X67 )
      | ( r1_tarski @ ( k5_relat_1 @ X68 @ X69 ) @ ( k5_relat_1 @ X66 @ X67 ) )
      | ~ ( r1_tarski @ X69 @ X67 )
      | ~ ( r1_tarski @ X68 @ X66 )
      | ~ ( v1_relat_1 @ X69 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X57 @ X58 ) )
      = ( k3_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X57 @ X58 ) )
      = ( k3_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['55','56','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EoAb1EZK0q
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 16:48:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 10.78/10.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.78/10.98  % Solved by: fo/fo7.sh
% 10.78/10.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.78/10.98  % done 12133 iterations in 10.525s
% 10.78/10.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.78/10.98  % SZS output start Refutation
% 10.78/10.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.78/10.98  thf(sk_A_type, type, sk_A: $i).
% 10.78/10.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.78/10.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.78/10.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.78/10.98  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 10.78/10.98  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 10.78/10.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.78/10.98  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 10.78/10.98                                           $i > $i).
% 10.78/10.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.78/10.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 10.78/10.98  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 10.78/10.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.78/10.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 10.78/10.98                                               $i > $i > $i > $o).
% 10.78/10.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.78/10.98  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 10.78/10.98  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 10.78/10.98  thf(sk_B_type, type, sk_B: $i).
% 10.78/10.98  thf(sk_C_type, type, sk_C: $i).
% 10.78/10.98  thf(t17_xboole_1, axiom,
% 10.78/10.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 10.78/10.98  thf('0', plain,
% 10.78/10.98      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 10.78/10.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 10.78/10.98  thf(t12_setfam_1, axiom,
% 10.78/10.98    (![A:$i,B:$i]:
% 10.78/10.98     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 10.78/10.98  thf('1', plain,
% 10.78/10.98      (![X57 : $i, X58 : $i]:
% 10.78/10.98         ((k1_setfam_1 @ (k2_tarski @ X57 @ X58)) = (k3_xboole_0 @ X57 @ X58))),
% 10.78/10.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.78/10.98  thf('2', plain,
% 10.78/10.98      (![X3 : $i, X4 : $i]:
% 10.78/10.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 10.78/10.98      inference('demod', [status(thm)], ['0', '1'])).
% 10.78/10.98  thf(t70_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 10.78/10.98  thf('3', plain,
% 10.78/10.98      (![X8 : $i, X9 : $i]:
% 10.78/10.98         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 10.78/10.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.78/10.98  thf(t71_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i]:
% 10.78/10.98     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 10.78/10.98  thf('4', plain,
% 10.78/10.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.78/10.98         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 10.78/10.98           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 10.78/10.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.78/10.98  thf(t72_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i,D:$i]:
% 10.78/10.98     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 10.78/10.98  thf('5', plain,
% 10.78/10.98      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 10.78/10.98         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 10.78/10.98           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 10.78/10.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.78/10.98  thf(t73_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 10.78/10.98     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 10.78/10.98       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 10.78/10.98  thf('6', plain,
% 10.78/10.98      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 10.78/10.98         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 10.78/10.98           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 10.78/10.98      inference('cnf', [status(esa)], [t73_enumset1])).
% 10.78/10.98  thf(t74_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.78/10.98     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 10.78/10.98       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 10.78/10.98  thf('7', plain,
% 10.78/10.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 10.78/10.98         ((k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 10.78/10.98           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 10.78/10.98      inference('cnf', [status(esa)], [t74_enumset1])).
% 10.78/10.98  thf(t75_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 10.78/10.98     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 10.78/10.98       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 10.78/10.98  thf('8', plain,
% 10.78/10.98      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 10.78/10.98         ((k6_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 10.78/10.98           = (k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 10.78/10.98      inference('cnf', [status(esa)], [t75_enumset1])).
% 10.78/10.98  thf(d6_enumset1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 10.78/10.98     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 10.78/10.98       ( ![J:$i]:
% 10.78/10.98         ( ( r2_hidden @ J @ I ) <=>
% 10.78/10.98           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 10.78/10.98                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 10.78/10.98                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 10.78/10.98  thf(zf_stmt_0, type, zip_tseitin_0 :
% 10.78/10.98      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 10.78/10.98  thf(zf_stmt_1, axiom,
% 10.78/10.98    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 10.78/10.98     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 10.78/10.98       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 10.78/10.98         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 10.78/10.98         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 10.78/10.98  thf(zf_stmt_2, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 10.78/10.98     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 10.78/10.98       ( ![J:$i]:
% 10.78/10.98         ( ( r2_hidden @ J @ I ) <=>
% 10.78/10.98           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 10.78/10.98  thf('9', plain,
% 10.78/10.98      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 10.78/10.98         X52 : $i, X53 : $i, X54 : $i]:
% 10.78/10.98         ((zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 10.78/10.98          | (r2_hidden @ X45 @ X54)
% 10.78/10.98          | ((X54)
% 10.78/10.98              != (k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46)))),
% 10.78/10.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.78/10.98  thf('10', plain,
% 10.78/10.98      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 10.78/10.98         X52 : $i, X53 : $i]:
% 10.78/10.98         ((r2_hidden @ X45 @ 
% 10.78/10.98           (k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46))
% 10.78/10.98          | (zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ 
% 10.78/10.98             X53))),
% 10.78/10.98      inference('simplify', [status(thm)], ['9'])).
% 10.78/10.98  thf('11', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 10.78/10.98         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 10.78/10.98          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 10.78/10.98      inference('sup+', [status(thm)], ['8', '10'])).
% 10.78/10.98  thf('12', plain,
% 10.78/10.98      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 10.78/10.98         X42 : $i, X43 : $i]:
% 10.78/10.98         (((X36) != (X37))
% 10.78/10.98          | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ 
% 10.78/10.98               X35))),
% 10.78/10.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.78/10.98  thf('13', plain,
% 10.78/10.98      (![X35 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 10.78/10.98         X43 : $i]:
% 10.78/10.98         ~ (zip_tseitin_0 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X35)),
% 10.78/10.98      inference('simplify', [status(thm)], ['12'])).
% 10.78/10.98  thf('14', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 10.78/10.98         (r2_hidden @ X6 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 10.78/10.98      inference('sup-', [status(thm)], ['11', '13'])).
% 10.78/10.98  thf('15', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.78/10.98         (r2_hidden @ X0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 10.78/10.98      inference('sup+', [status(thm)], ['7', '14'])).
% 10.78/10.98  thf('16', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.78/10.98         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 10.78/10.98      inference('sup+', [status(thm)], ['6', '15'])).
% 10.78/10.98  thf('17', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.78/10.98         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 10.78/10.98      inference('sup+', [status(thm)], ['5', '16'])).
% 10.78/10.98  thf('18', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 10.78/10.98      inference('sup+', [status(thm)], ['4', '17'])).
% 10.78/10.98  thf('19', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 10.78/10.98      inference('sup+', [status(thm)], ['3', '18'])).
% 10.78/10.98  thf(t4_setfam_1, axiom,
% 10.78/10.98    (![A:$i,B:$i]:
% 10.78/10.98     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 10.78/10.98  thf('20', plain,
% 10.78/10.98      (![X62 : $i, X63 : $i]:
% 10.78/10.98         ((r1_tarski @ (k1_setfam_1 @ X62) @ X63) | ~ (r2_hidden @ X63 @ X62))),
% 10.78/10.98      inference('cnf', [status(esa)], [t4_setfam_1])).
% 10.78/10.98  thf('21', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 10.78/10.98      inference('sup-', [status(thm)], ['19', '20'])).
% 10.78/10.98  thf(t19_xboole_1, axiom,
% 10.78/10.98    (![A:$i,B:$i,C:$i]:
% 10.78/10.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 10.78/10.98       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 10.78/10.98  thf('22', plain,
% 10.78/10.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.78/10.98         (~ (r1_tarski @ X5 @ X6)
% 10.78/10.98          | ~ (r1_tarski @ X5 @ X7)
% 10.78/10.98          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 10.78/10.98      inference('cnf', [status(esa)], [t19_xboole_1])).
% 10.78/10.98  thf('23', plain,
% 10.78/10.98      (![X57 : $i, X58 : $i]:
% 10.78/10.98         ((k1_setfam_1 @ (k2_tarski @ X57 @ X58)) = (k3_xboole_0 @ X57 @ X58))),
% 10.78/10.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.78/10.98  thf('24', plain,
% 10.78/10.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.78/10.98         (~ (r1_tarski @ X5 @ X6)
% 10.78/10.98          | ~ (r1_tarski @ X5 @ X7)
% 10.78/10.98          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 10.78/10.98      inference('demod', [status(thm)], ['22', '23'])).
% 10.78/10.98  thf('25', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 10.78/10.98           (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))
% 10.78/10.98          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2))),
% 10.78/10.98      inference('sup-', [status(thm)], ['21', '24'])).
% 10.78/10.98  thf('26', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 10.78/10.98          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 10.78/10.98      inference('sup-', [status(thm)], ['2', '25'])).
% 10.78/10.98  thf(d10_xboole_0, axiom,
% 10.78/10.98    (![A:$i,B:$i]:
% 10.78/10.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.78/10.98  thf('27', plain,
% 10.78/10.98      (![X0 : $i, X2 : $i]:
% 10.78/10.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.78/10.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.78/10.98  thf('28', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 10.78/10.98             (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 10.78/10.98          | ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 10.78/10.98              = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 10.78/10.98      inference('sup-', [status(thm)], ['26', '27'])).
% 10.78/10.98  thf('29', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 10.78/10.98          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 10.78/10.98      inference('sup-', [status(thm)], ['2', '25'])).
% 10.78/10.98  thf('30', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 10.78/10.98           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 10.78/10.98      inference('demod', [status(thm)], ['28', '29'])).
% 10.78/10.98  thf('31', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 10.78/10.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.78/10.98  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.78/10.98      inference('simplify', [status(thm)], ['31'])).
% 10.78/10.98  thf('33', plain,
% 10.78/10.98      (![X3 : $i, X4 : $i]:
% 10.78/10.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 10.78/10.98      inference('demod', [status(thm)], ['0', '1'])).
% 10.78/10.98  thf(t3_subset, axiom,
% 10.78/10.98    (![A:$i,B:$i]:
% 10.78/10.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.78/10.98  thf('34', plain,
% 10.78/10.98      (![X59 : $i, X61 : $i]:
% 10.78/10.98         ((m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X61)) | ~ (r1_tarski @ X59 @ X61))),
% 10.78/10.98      inference('cnf', [status(esa)], [t3_subset])).
% 10.78/10.98  thf('35', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 10.78/10.98          (k1_zfmisc_1 @ X0))),
% 10.78/10.98      inference('sup-', [status(thm)], ['33', '34'])).
% 10.78/10.98  thf(cc2_relat_1, axiom,
% 10.78/10.98    (![A:$i]:
% 10.78/10.98     ( ( v1_relat_1 @ A ) =>
% 10.78/10.98       ( ![B:$i]:
% 10.78/10.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.78/10.98  thf('36', plain,
% 10.78/10.98      (![X64 : $i, X65 : $i]:
% 10.78/10.98         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X65))
% 10.78/10.98          | (v1_relat_1 @ X64)
% 10.78/10.98          | ~ (v1_relat_1 @ X65))),
% 10.78/10.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.78/10.98  thf('37', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X0)
% 10.78/10.98          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 10.78/10.98      inference('sup-', [status(thm)], ['35', '36'])).
% 10.78/10.98  thf('38', plain,
% 10.78/10.98      (![X3 : $i, X4 : $i]:
% 10.78/10.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 10.78/10.98      inference('demod', [status(thm)], ['0', '1'])).
% 10.78/10.98  thf(t50_relat_1, axiom,
% 10.78/10.98    (![A:$i]:
% 10.78/10.98     ( ( v1_relat_1 @ A ) =>
% 10.78/10.98       ( ![B:$i]:
% 10.78/10.98         ( ( v1_relat_1 @ B ) =>
% 10.78/10.98           ( ![C:$i]:
% 10.78/10.98             ( ( v1_relat_1 @ C ) =>
% 10.78/10.98               ( ![D:$i]:
% 10.78/10.98                 ( ( v1_relat_1 @ D ) =>
% 10.78/10.98                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 10.78/10.98                     ( r1_tarski @
% 10.78/10.98                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 10.78/10.98  thf('39', plain,
% 10.78/10.98      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X66)
% 10.78/10.98          | ~ (v1_relat_1 @ X67)
% 10.78/10.98          | (r1_tarski @ (k5_relat_1 @ X68 @ X69) @ (k5_relat_1 @ X66 @ X67))
% 10.78/10.98          | ~ (r1_tarski @ X69 @ X67)
% 10.78/10.98          | ~ (r1_tarski @ X68 @ X66)
% 10.78/10.98          | ~ (v1_relat_1 @ X69)
% 10.78/10.98          | ~ (v1_relat_1 @ X68))),
% 10.78/10.98      inference('cnf', [status(esa)], [t50_relat_1])).
% 10.78/10.98  thf('40', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X2)
% 10.78/10.98          | ~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 10.78/10.98          | ~ (r1_tarski @ X2 @ X3)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 10.78/10.98             (k5_relat_1 @ X3 @ X0))
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | ~ (v1_relat_1 @ X3))),
% 10.78/10.98      inference('sup-', [status(thm)], ['38', '39'])).
% 10.78/10.98  thf('41', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X1)
% 10.78/10.98          | ~ (v1_relat_1 @ X2)
% 10.78/10.98          | ~ (v1_relat_1 @ X1)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 10.78/10.98             (k5_relat_1 @ X2 @ X1))
% 10.78/10.98          | ~ (r1_tarski @ X3 @ X2)
% 10.78/10.98          | ~ (v1_relat_1 @ X3))),
% 10.78/10.98      inference('sup-', [status(thm)], ['37', '40'])).
% 10.78/10.98  thf('42', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X3)
% 10.78/10.98          | ~ (r1_tarski @ X3 @ X2)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 10.78/10.98             (k5_relat_1 @ X2 @ X1))
% 10.78/10.98          | ~ (v1_relat_1 @ X2)
% 10.78/10.98          | ~ (v1_relat_1 @ X1))),
% 10.78/10.98      inference('simplify', [status(thm)], ['41'])).
% 10.78/10.98  thf('43', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X1)
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 10.78/10.98             (k5_relat_1 @ X0 @ X1))
% 10.78/10.98          | ~ (v1_relat_1 @ X0))),
% 10.78/10.98      inference('sup-', [status(thm)], ['32', '42'])).
% 10.78/10.98  thf('44', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         ((r1_tarski @ 
% 10.78/10.98           (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 10.78/10.98           (k5_relat_1 @ X0 @ X1))
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | ~ (v1_relat_1 @ X1))),
% 10.78/10.98      inference('simplify', [status(thm)], ['43'])).
% 10.78/10.98  thf('45', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         ((r1_tarski @ 
% 10.78/10.98           (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 10.78/10.98           (k5_relat_1 @ X2 @ X0))
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | ~ (v1_relat_1 @ X2))),
% 10.78/10.98      inference('sup+', [status(thm)], ['30', '44'])).
% 10.78/10.98  thf('46', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         ((r1_tarski @ 
% 10.78/10.98           (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 10.78/10.98           (k5_relat_1 @ X0 @ X1))
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | ~ (v1_relat_1 @ X1))),
% 10.78/10.98      inference('simplify', [status(thm)], ['43'])).
% 10.78/10.98  thf('47', plain,
% 10.78/10.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.78/10.98         (~ (r1_tarski @ X5 @ X6)
% 10.78/10.98          | ~ (r1_tarski @ X5 @ X7)
% 10.78/10.98          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 10.78/10.98      inference('demod', [status(thm)], ['22', '23'])).
% 10.78/10.98  thf('48', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X0)
% 10.78/10.98          | ~ (v1_relat_1 @ X1)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 10.78/10.98             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 10.78/10.98          | ~ (r1_tarski @ 
% 10.78/10.98               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 10.78/10.98      inference('sup-', [status(thm)], ['46', '47'])).
% 10.78/10.98  thf('49', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X1)
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 10.78/10.98             (k1_setfam_1 @ 
% 10.78/10.98              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 10.78/10.98          | ~ (v1_relat_1 @ X1)
% 10.78/10.98          | ~ (v1_relat_1 @ X2))),
% 10.78/10.98      inference('sup-', [status(thm)], ['45', '48'])).
% 10.78/10.98  thf('50', plain,
% 10.78/10.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.78/10.98         (~ (v1_relat_1 @ X2)
% 10.78/10.98          | (r1_tarski @ 
% 10.78/10.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 10.78/10.98             (k1_setfam_1 @ 
% 10.78/10.98              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 10.78/10.98          | ~ (v1_relat_1 @ X0)
% 10.78/10.98          | ~ (v1_relat_1 @ X1))),
% 10.78/10.98      inference('simplify', [status(thm)], ['49'])).
% 10.78/10.98  thf(t52_relat_1, conjecture,
% 10.78/10.98    (![A:$i]:
% 10.78/10.98     ( ( v1_relat_1 @ A ) =>
% 10.78/10.98       ( ![B:$i]:
% 10.78/10.98         ( ( v1_relat_1 @ B ) =>
% 10.78/10.98           ( ![C:$i]:
% 10.78/10.98             ( ( v1_relat_1 @ C ) =>
% 10.78/10.98               ( r1_tarski @
% 10.78/10.98                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 10.78/10.98                 ( k3_xboole_0 @
% 10.78/10.98                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 10.78/10.98  thf(zf_stmt_3, negated_conjecture,
% 10.78/10.98    (~( ![A:$i]:
% 10.78/10.98        ( ( v1_relat_1 @ A ) =>
% 10.78/10.98          ( ![B:$i]:
% 10.78/10.98            ( ( v1_relat_1 @ B ) =>
% 10.78/10.98              ( ![C:$i]:
% 10.78/10.98                ( ( v1_relat_1 @ C ) =>
% 10.78/10.98                  ( r1_tarski @
% 10.78/10.98                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 10.78/10.98                    ( k3_xboole_0 @
% 10.78/10.98                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 10.78/10.98    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 10.78/10.98  thf('51', plain,
% 10.78/10.98      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 10.78/10.98          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 10.78/10.98           (k5_relat_1 @ sk_A @ sk_C)))),
% 10.78/10.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.78/10.98  thf('52', plain,
% 10.78/10.98      (![X57 : $i, X58 : $i]:
% 10.78/10.98         ((k1_setfam_1 @ (k2_tarski @ X57 @ X58)) = (k3_xboole_0 @ X57 @ X58))),
% 10.78/10.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.78/10.98  thf('53', plain,
% 10.78/10.98      (![X57 : $i, X58 : $i]:
% 10.78/10.98         ((k1_setfam_1 @ (k2_tarski @ X57 @ X58)) = (k3_xboole_0 @ X57 @ X58))),
% 10.78/10.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.78/10.98  thf('54', plain,
% 10.78/10.98      (~ (r1_tarski @ 
% 10.78/10.98          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 10.78/10.98          (k1_setfam_1 @ 
% 10.78/10.98           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 10.78/10.98      inference('demod', [status(thm)], ['51', '52', '53'])).
% 10.78/10.98  thf('55', plain,
% 10.78/10.98      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 10.78/10.98      inference('sup-', [status(thm)], ['50', '54'])).
% 10.78/10.98  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 10.78/10.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.78/10.98  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 10.78/10.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.78/10.98  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 10.78/10.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.78/10.98  thf('59', plain, ($false),
% 10.78/10.98      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 10.78/10.98  
% 10.78/10.98  % SZS output end Refutation
% 10.78/10.98  
% 10.78/10.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
