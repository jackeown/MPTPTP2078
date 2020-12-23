%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiwkuoMPux

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:11 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 136 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  874 (1430 expanded)
%              Number of equality atoms :   37 (  65 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k6_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
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

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      | ( r2_hidden @ X42 @ X51 )
      | ( X51
       != ( k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X42 @ ( k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 ) )
      | ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X33 != X34 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X59 ) @ X60 )
      | ~ ( r2_hidden @ X60 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X56: $i,X58: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( r1_tarski @ X64 @ X63 )
      | ( r1_tarski @ ( k5_relat_1 @ X65 @ X64 ) @ ( k5_relat_1 @ X65 @ X63 ) )
      | ~ ( v1_relat_1 @ X65 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X56: $i,X58: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( r1_tarski @ X64 @ X63 )
      | ( r1_tarski @ ( k5_relat_1 @ X65 @ X64 ) @ ( k5_relat_1 @ X65 @ X63 ) )
      | ~ ( v1_relat_1 @ X65 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('41',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

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

thf('46',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['50','51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiwkuoMPux
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.21/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.45  % Solved by: fo/fo7.sh
% 1.21/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.45  % done 1839 iterations in 0.998s
% 1.21/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.45  % SZS output start Refutation
% 1.21/1.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.21/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.21/1.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.21/1.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.21/1.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.21/1.45                                               $i > $i > $i > $o).
% 1.21/1.45  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.21/1.45  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.21/1.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.21/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.21/1.45  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.21/1.45                                           $i > $i).
% 1.21/1.45  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.21/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.21/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.45  thf(t70_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.21/1.45  thf('0', plain,
% 1.21/1.45      (![X5 : $i, X6 : $i]:
% 1.21/1.45         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 1.21/1.45      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.21/1.45  thf(t71_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.21/1.45  thf('1', plain,
% 1.21/1.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.21/1.45         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.21/1.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.21/1.45  thf(t72_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.21/1.45     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.21/1.45  thf('2', plain,
% 1.21/1.45      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.21/1.45         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 1.21/1.45           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 1.21/1.45      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.21/1.45  thf(t73_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.21/1.45     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.21/1.45       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.21/1.45  thf('3', plain,
% 1.21/1.45      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.21/1.45         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 1.21/1.45           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 1.21/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.21/1.45  thf(t74_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.21/1.45     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.21/1.45       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.21/1.45  thf('4', plain,
% 1.21/1.45      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.21/1.45         ((k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 1.21/1.45           = (k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 1.21/1.45      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.21/1.45  thf(t75_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.21/1.45     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.21/1.45       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.21/1.45  thf('5', plain,
% 1.21/1.45      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.21/1.45         ((k6_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 1.21/1.45           = (k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 1.21/1.45      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.21/1.45  thf(d6_enumset1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.21/1.45     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.21/1.45       ( ![J:$i]:
% 1.21/1.45         ( ( r2_hidden @ J @ I ) <=>
% 1.21/1.45           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 1.21/1.45                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 1.21/1.45                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 1.21/1.45  thf(zf_stmt_0, type, zip_tseitin_0 :
% 1.21/1.45      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.21/1.45  thf(zf_stmt_1, axiom,
% 1.21/1.45    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.21/1.45     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.21/1.45       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 1.21/1.45         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 1.21/1.45         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 1.21/1.45  thf(zf_stmt_2, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.21/1.45     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.21/1.45       ( ![J:$i]:
% 1.21/1.45         ( ( r2_hidden @ J @ I ) <=>
% 1.21/1.45           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.21/1.45  thf('6', plain,
% 1.21/1.45      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 1.21/1.45         X49 : $i, X50 : $i, X51 : $i]:
% 1.21/1.45         ((zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 1.21/1.45          | (r2_hidden @ X42 @ X51)
% 1.21/1.45          | ((X51)
% 1.21/1.45              != (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.21/1.45  thf('7', plain,
% 1.21/1.45      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 1.21/1.45         X49 : $i, X50 : $i]:
% 1.21/1.45         ((r2_hidden @ X42 @ 
% 1.21/1.45           (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43))
% 1.21/1.45          | (zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ 
% 1.21/1.45             X50))),
% 1.21/1.45      inference('simplify', [status(thm)], ['6'])).
% 1.21/1.45  thf('8', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.21/1.45         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.21/1.45          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.21/1.45      inference('sup+', [status(thm)], ['5', '7'])).
% 1.21/1.45  thf('9', plain,
% 1.21/1.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 1.21/1.45         X39 : $i, X40 : $i]:
% 1.21/1.45         (((X33) != (X34))
% 1.21/1.45          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 1.21/1.45               X32))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.21/1.45  thf('10', plain,
% 1.21/1.45      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 1.21/1.45         X40 : $i]:
% 1.21/1.45         ~ (zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32)),
% 1.21/1.45      inference('simplify', [status(thm)], ['9'])).
% 1.21/1.45  thf('11', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.21/1.45         (r2_hidden @ X6 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 1.21/1.45      inference('sup-', [status(thm)], ['8', '10'])).
% 1.21/1.45  thf('12', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.21/1.45         (r2_hidden @ X0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['4', '11'])).
% 1.21/1.45  thf('13', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.21/1.45         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['3', '12'])).
% 1.21/1.45  thf('14', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.21/1.45         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['2', '13'])).
% 1.21/1.45  thf('15', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['1', '14'])).
% 1.21/1.45  thf('16', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['0', '15'])).
% 1.21/1.45  thf(t4_setfam_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.21/1.45  thf('17', plain,
% 1.21/1.45      (![X59 : $i, X60 : $i]:
% 1.21/1.45         ((r1_tarski @ (k1_setfam_1 @ X59) @ X60) | ~ (r2_hidden @ X60 @ X59))),
% 1.21/1.45      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.21/1.45  thf('18', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.21/1.45      inference('sup-', [status(thm)], ['16', '17'])).
% 1.21/1.45  thf(t3_subset, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.21/1.45  thf('19', plain,
% 1.21/1.45      (![X56 : $i, X58 : $i]:
% 1.21/1.45         ((m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X56 @ X58))),
% 1.21/1.45      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.45  thf('20', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.21/1.45          (k1_zfmisc_1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['18', '19'])).
% 1.21/1.45  thf(cc2_relat_1, axiom,
% 1.21/1.45    (![A:$i]:
% 1.21/1.45     ( ( v1_relat_1 @ A ) =>
% 1.21/1.45       ( ![B:$i]:
% 1.21/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.21/1.45  thf('21', plain,
% 1.21/1.45      (![X61 : $i, X62 : $i]:
% 1.21/1.45         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 1.21/1.45          | (v1_relat_1 @ X61)
% 1.21/1.45          | ~ (v1_relat_1 @ X62))),
% 1.21/1.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.21/1.45  thf('22', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X0)
% 1.21/1.45          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['20', '21'])).
% 1.21/1.45  thf('23', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.21/1.45      inference('sup-', [status(thm)], ['16', '17'])).
% 1.21/1.45  thf(t48_relat_1, axiom,
% 1.21/1.45    (![A:$i]:
% 1.21/1.45     ( ( v1_relat_1 @ A ) =>
% 1.21/1.45       ( ![B:$i]:
% 1.21/1.45         ( ( v1_relat_1 @ B ) =>
% 1.21/1.45           ( ![C:$i]:
% 1.21/1.45             ( ( v1_relat_1 @ C ) =>
% 1.21/1.45               ( ( r1_tarski @ A @ B ) =>
% 1.21/1.45                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 1.21/1.45  thf('24', plain,
% 1.21/1.45      (![X63 : $i, X64 : $i, X65 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X63)
% 1.21/1.45          | ~ (r1_tarski @ X64 @ X63)
% 1.21/1.45          | (r1_tarski @ (k5_relat_1 @ X65 @ X64) @ (k5_relat_1 @ X65 @ X63))
% 1.21/1.45          | ~ (v1_relat_1 @ X65)
% 1.21/1.45          | ~ (v1_relat_1 @ X64))),
% 1.21/1.45      inference('cnf', [status(esa)], [t48_relat_1])).
% 1.21/1.45  thf('25', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.21/1.45          | ~ (v1_relat_1 @ X2)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ X0))
% 1.21/1.45          | ~ (v1_relat_1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['23', '24'])).
% 1.21/1.45  thf('26', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X0)
% 1.21/1.45          | ~ (v1_relat_1 @ X0)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ X0))
% 1.21/1.45          | ~ (v1_relat_1 @ X2))),
% 1.21/1.45      inference('sup-', [status(thm)], ['22', '25'])).
% 1.21/1.45  thf('27', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X2)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ X0))
% 1.21/1.45          | ~ (v1_relat_1 @ X0))),
% 1.21/1.45      inference('simplify', [status(thm)], ['26'])).
% 1.21/1.45  thf(t17_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.21/1.45  thf('28', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.21/1.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.21/1.45  thf(t12_setfam_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.21/1.45  thf('29', plain,
% 1.21/1.45      (![X54 : $i, X55 : $i]:
% 1.21/1.45         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.21/1.45  thf('30', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 1.21/1.45      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.45  thf('31', plain,
% 1.21/1.45      (![X56 : $i, X58 : $i]:
% 1.21/1.45         ((m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X56 @ X58))),
% 1.21/1.45      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.45  thf('32', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 1.21/1.45          (k1_zfmisc_1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.21/1.45  thf('33', plain,
% 1.21/1.45      (![X61 : $i, X62 : $i]:
% 1.21/1.45         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 1.21/1.45          | (v1_relat_1 @ X61)
% 1.21/1.45          | ~ (v1_relat_1 @ X62))),
% 1.21/1.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.21/1.45  thf('34', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X0)
% 1.21/1.45          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.21/1.45      inference('sup-', [status(thm)], ['32', '33'])).
% 1.21/1.45  thf('35', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 1.21/1.45      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.45  thf('36', plain,
% 1.21/1.45      (![X63 : $i, X64 : $i, X65 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X63)
% 1.21/1.45          | ~ (r1_tarski @ X64 @ X63)
% 1.21/1.45          | (r1_tarski @ (k5_relat_1 @ X65 @ X64) @ (k5_relat_1 @ X65 @ X63))
% 1.21/1.45          | ~ (v1_relat_1 @ X65)
% 1.21/1.45          | ~ (v1_relat_1 @ X64))),
% 1.21/1.45      inference('cnf', [status(esa)], [t48_relat_1])).
% 1.21/1.45  thf('37', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 1.21/1.45          | ~ (v1_relat_1 @ X2)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ X0))
% 1.21/1.45          | ~ (v1_relat_1 @ X0))),
% 1.21/1.45      inference('sup-', [status(thm)], ['35', '36'])).
% 1.21/1.45  thf('38', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X1)
% 1.21/1.45          | ~ (v1_relat_1 @ X1)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ X1))
% 1.21/1.45          | ~ (v1_relat_1 @ X2))),
% 1.21/1.45      inference('sup-', [status(thm)], ['34', '37'])).
% 1.21/1.45  thf('39', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X2)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.21/1.45             (k5_relat_1 @ X2 @ X1))
% 1.21/1.45          | ~ (v1_relat_1 @ X1))),
% 1.21/1.45      inference('simplify', [status(thm)], ['38'])).
% 1.21/1.45  thf(t19_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.21/1.45       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.21/1.45  thf('40', plain,
% 1.21/1.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.21/1.45         (~ (r1_tarski @ X2 @ X3)
% 1.21/1.45          | ~ (r1_tarski @ X2 @ X4)
% 1.21/1.45          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.21/1.45  thf('41', plain,
% 1.21/1.45      (![X54 : $i, X55 : $i]:
% 1.21/1.45         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.21/1.45  thf('42', plain,
% 1.21/1.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.21/1.45         (~ (r1_tarski @ X2 @ X3)
% 1.21/1.45          | ~ (r1_tarski @ X2 @ X4)
% 1.21/1.45          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 1.21/1.45      inference('demod', [status(thm)], ['40', '41'])).
% 1.21/1.45  thf('43', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X0)
% 1.21/1.45          | ~ (v1_relat_1 @ X1)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 1.21/1.45             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 1.21/1.45          | ~ (r1_tarski @ 
% 1.21/1.45               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 1.21/1.45      inference('sup-', [status(thm)], ['39', '42'])).
% 1.21/1.45  thf('44', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X0)
% 1.21/1.45          | ~ (v1_relat_1 @ X1)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 1.21/1.45             (k1_setfam_1 @ 
% 1.21/1.45              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 1.21/1.45          | ~ (v1_relat_1 @ X1)
% 1.21/1.45          | ~ (v1_relat_1 @ X2))),
% 1.21/1.45      inference('sup-', [status(thm)], ['27', '43'])).
% 1.21/1.45  thf('45', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (~ (v1_relat_1 @ X2)
% 1.21/1.45          | (r1_tarski @ 
% 1.21/1.45             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 1.21/1.45             (k1_setfam_1 @ 
% 1.21/1.45              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 1.21/1.45          | ~ (v1_relat_1 @ X1)
% 1.21/1.45          | ~ (v1_relat_1 @ X0))),
% 1.21/1.45      inference('simplify', [status(thm)], ['44'])).
% 1.21/1.45  thf(t52_relat_1, conjecture,
% 1.21/1.45    (![A:$i]:
% 1.21/1.45     ( ( v1_relat_1 @ A ) =>
% 1.21/1.45       ( ![B:$i]:
% 1.21/1.45         ( ( v1_relat_1 @ B ) =>
% 1.21/1.45           ( ![C:$i]:
% 1.21/1.45             ( ( v1_relat_1 @ C ) =>
% 1.21/1.45               ( r1_tarski @
% 1.21/1.45                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.21/1.45                 ( k3_xboole_0 @
% 1.21/1.45                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.21/1.45  thf(zf_stmt_3, negated_conjecture,
% 1.21/1.45    (~( ![A:$i]:
% 1.21/1.45        ( ( v1_relat_1 @ A ) =>
% 1.21/1.45          ( ![B:$i]:
% 1.21/1.45            ( ( v1_relat_1 @ B ) =>
% 1.21/1.45              ( ![C:$i]:
% 1.21/1.45                ( ( v1_relat_1 @ C ) =>
% 1.21/1.45                  ( r1_tarski @
% 1.21/1.45                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.21/1.45                    ( k3_xboole_0 @
% 1.21/1.45                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 1.21/1.45    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 1.21/1.45  thf('46', plain,
% 1.21/1.45      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.21/1.45          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 1.21/1.45           (k5_relat_1 @ sk_A @ sk_C)))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.21/1.45  thf('47', plain,
% 1.21/1.45      (![X54 : $i, X55 : $i]:
% 1.21/1.45         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.21/1.45  thf('48', plain,
% 1.21/1.45      (![X54 : $i, X55 : $i]:
% 1.21/1.45         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 1.21/1.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.21/1.45  thf('49', plain,
% 1.21/1.45      (~ (r1_tarski @ 
% 1.21/1.45          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 1.21/1.45          (k1_setfam_1 @ 
% 1.21/1.45           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 1.21/1.45      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.21/1.45  thf('50', plain,
% 1.21/1.45      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.21/1.45      inference('sup-', [status(thm)], ['45', '49'])).
% 1.21/1.45  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.21/1.45  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.21/1.45  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.21/1.45  thf('54', plain, ($false),
% 1.21/1.45      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.21/1.45  
% 1.21/1.45  % SZS output end Refutation
% 1.21/1.45  
% 1.21/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
