%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cmG8wZ5p4G

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:03 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  761 (1255 expanded)
%              Number of equality atoms :   37 (  65 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ( r1_tarski @ ( k3_relat_1 @ X64 ) @ ( k3_relat_1 @ X63 ) )
      | ~ ( r1_tarski @ X64 @ X63 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X56: $i,X58: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ( r1_tarski @ ( k3_relat_1 @ X64 ) @ ( k3_relat_1 @ X63 ) )
      | ~ ( r1_tarski @ X64 @ X63 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X56: $i,X58: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','36'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cmG8wZ5p4G
% 0.16/0.37  % Computer   : n020.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 491 iterations in 0.224s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.52/0.71                                               $i > $i > $i > $o).
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.52/0.71  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.71  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.52/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.52/0.71  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.52/0.71                                           $i > $i).
% 0.52/0.71  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.71  thf(t70_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      (![X5 : $i, X6 : $i]:
% 0.52/0.71         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.52/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.71  thf(t71_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.71         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.52/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.52/0.71  thf(t72_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.71         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.52/0.71           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.52/0.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.52/0.71  thf(t73_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.52/0.71     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.52/0.71       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.71         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.52/0.71           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.52/0.71  thf(t74_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.71     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.52/0.71       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.71         ((k5_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.52/0.71           = (k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.52/0.71      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.52/0.71  thf(t75_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.52/0.71     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.52/0.71       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.71         ((k6_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.52/0.71           = (k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.52/0.71      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.52/0.71  thf(d6_enumset1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.52/0.71       ( ![J:$i]:
% 0.52/0.71         ( ( r2_hidden @ J @ I ) <=>
% 0.52/0.71           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.52/0.71                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.52/0.71                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.52/0.71      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.52/0.71  thf(zf_stmt_1, axiom,
% 0.52/0.71    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.52/0.71     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.52/0.71       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.52/0.71         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.52/0.71         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_2, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.52/0.71     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.52/0.71       ( ![J:$i]:
% 0.52/0.71         ( ( r2_hidden @ J @ I ) <=>
% 0.52/0.71           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.52/0.71         X49 : $i, X50 : $i, X51 : $i]:
% 0.52/0.71         ((zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.52/0.71          | (r2_hidden @ X42 @ X51)
% 0.52/0.71          | ((X51)
% 0.52/0.71              != (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.52/0.71         X49 : $i, X50 : $i]:
% 0.52/0.71         ((r2_hidden @ X42 @ 
% 0.52/0.71           (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43))
% 0.52/0.71          | (zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ 
% 0.52/0.71             X50))),
% 0.52/0.71      inference('simplify', [status(thm)], ['6'])).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.71         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.52/0.71          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.52/0.71      inference('sup+', [status(thm)], ['5', '7'])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.52/0.71         X39 : $i, X40 : $i]:
% 0.52/0.71         (((X33) != (X34))
% 0.52/0.71          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.52/0.71               X32))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.52/0.71         X40 : $i]:
% 0.52/0.71         ~ (zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32)),
% 0.52/0.71      inference('simplify', [status(thm)], ['9'])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.71         (r2_hidden @ X6 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.52/0.71      inference('sup-', [status(thm)], ['8', '10'])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.52/0.71         (r2_hidden @ X0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['4', '11'])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['3', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.71         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['2', '13'])).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['1', '14'])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['0', '15'])).
% 0.52/0.71  thf(t4_setfam_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X59 : $i, X60 : $i]:
% 0.52/0.71         ((r1_tarski @ (k1_setfam_1 @ X59) @ X60) | ~ (r2_hidden @ X60 @ X59))),
% 0.52/0.71      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.71  thf(t31_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( v1_relat_1 @ B ) =>
% 0.52/0.71           ( ( r1_tarski @ A @ B ) =>
% 0.52/0.71             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X63 : $i, X64 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X63)
% 0.52/0.71          | (r1_tarski @ (k3_relat_1 @ X64) @ (k3_relat_1 @ X63))
% 0.52/0.71          | ~ (r1_tarski @ X64 @ X63)
% 0.52/0.71          | ~ (v1_relat_1 @ X64))),
% 0.52/0.71      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.52/0.71          | (r1_tarski @ 
% 0.52/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.52/0.71             (k3_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.71  thf(t3_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X56 : $i, X58 : $i]:
% 0.52/0.71         ((m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X56 @ X58))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.52/0.71          (k1_zfmisc_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf(cc2_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X61 : $i, X62 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 0.52/0.71          | (v1_relat_1 @ X61)
% 0.52/0.71          | ~ (v1_relat_1 @ X62))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | (r1_tarski @ 
% 0.52/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.52/0.71             (k3_relat_1 @ X0)))),
% 0.52/0.71      inference('clc', [status(thm)], ['20', '25'])).
% 0.52/0.71  thf(t17_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.52/0.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.71  thf(t12_setfam_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (![X54 : $i, X55 : $i]:
% 0.52/0.71         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.52/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      (![X63 : $i, X64 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X63)
% 0.52/0.71          | (r1_tarski @ (k3_relat_1 @ X64) @ (k3_relat_1 @ X63))
% 0.52/0.71          | ~ (r1_tarski @ X64 @ X63)
% 0.52/0.71          | ~ (v1_relat_1 @ X64))),
% 0.52/0.71      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.52/0.71          | (r1_tarski @ 
% 0.52/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.52/0.71             (k3_relat_1 @ X0))
% 0.52/0.71          | ~ (v1_relat_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.52/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X56 : $i, X58 : $i]:
% 0.52/0.71         ((m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X56 @ X58))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.52/0.71          (k1_zfmisc_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X61 : $i, X62 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 0.52/0.71          | (v1_relat_1 @ X61)
% 0.52/0.71          | ~ (v1_relat_1 @ X62))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | (r1_tarski @ 
% 0.52/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.52/0.71             (k3_relat_1 @ X0)))),
% 0.52/0.71      inference('clc', [status(thm)], ['31', '36'])).
% 0.52/0.71  thf(t19_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.52/0.71       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (~ (r1_tarski @ X2 @ X3)
% 0.52/0.71          | ~ (r1_tarski @ X2 @ X4)
% 0.52/0.71          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (![X54 : $i, X55 : $i]:
% 0.52/0.71         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (~ (r1_tarski @ X2 @ X3)
% 0.52/0.71          | ~ (r1_tarski @ X2 @ X4)
% 0.52/0.71          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.52/0.71      inference('demod', [status(thm)], ['38', '39'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | (r1_tarski @ 
% 0.52/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.52/0.71             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 0.52/0.71          | ~ (r1_tarski @ 
% 0.52/0.71               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['37', '40'])).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X0)
% 0.52/0.71          | (r1_tarski @ 
% 0.52/0.71             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.52/0.71             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 0.52/0.71          | ~ (v1_relat_1 @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['26', '41'])).
% 0.52/0.71  thf(t34_relat_1, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( v1_relat_1 @ B ) =>
% 0.52/0.71           ( r1_tarski @
% 0.52/0.71             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.52/0.71             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_3, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( v1_relat_1 @ A ) =>
% 0.52/0.71          ( ![B:$i]:
% 0.52/0.71            ( ( v1_relat_1 @ B ) =>
% 0.52/0.71              ( r1_tarski @
% 0.52/0.71                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.52/0.71                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.52/0.71          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X54 : $i, X55 : $i]:
% 0.52/0.71         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      (![X54 : $i, X55 : $i]:
% 0.52/0.71         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (~ (r1_tarski @ 
% 0.52/0.71          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.52/0.71          (k1_setfam_1 @ 
% 0.52/0.71           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 0.52/0.71      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.52/0.71  thf('47', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['42', '46'])).
% 0.52/0.71  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.71  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.71  thf('50', plain, ($false),
% 0.52/0.71      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
