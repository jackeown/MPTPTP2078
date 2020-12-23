%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tj8ttTs8gH

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Theorem 19.76s
% Output     : Refutation 19.76s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 164 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  785 (1569 expanded)
%              Number of equality atoms :   30 (  64 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
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

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      | ( r2_hidden @ X29 @ X35 )
      | ( X35
       != ( k3_enumset1 @ X34 @ X33 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X29 @ ( k3_enumset1 @ X34 @ X33 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X23 != X24 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X24 @ X25 @ X26 @ X27 @ X22 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('17',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k5_relat_1 @ X49 @ X50 ) @ ( k5_relat_1 @ X47 @ X48 ) )
      | ~ ( r1_tarski @ X50 @ X48 )
      | ~ ( r1_tarski @ X49 @ X47 )
      | ~ ( v1_relat_1 @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

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

thf('45',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tj8ttTs8gH
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 19.76/19.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.76/19.98  % Solved by: fo/fo7.sh
% 19.76/19.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.76/19.98  % done 18270 iterations in 19.515s
% 19.76/19.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.76/19.98  % SZS output start Refutation
% 19.76/19.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.76/19.98  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 19.76/19.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 19.76/19.98  thf(sk_C_type, type, sk_C: $i).
% 19.76/19.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 19.76/19.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 19.76/19.98  thf(sk_A_type, type, sk_A: $i).
% 19.76/19.98  thf(sk_B_type, type, sk_B: $i).
% 19.76/19.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.76/19.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.76/19.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 19.76/19.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.76/19.98  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 19.76/19.98  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 19.76/19.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.76/19.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.76/19.98  thf(t17_xboole_1, axiom,
% 19.76/19.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 19.76/19.98  thf('0', plain,
% 19.76/19.98      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 19.76/19.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 19.76/19.98  thf(t12_setfam_1, axiom,
% 19.76/19.98    (![A:$i,B:$i]:
% 19.76/19.98     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.76/19.98  thf('1', plain,
% 19.76/19.98      (![X38 : $i, X39 : $i]:
% 19.76/19.98         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 19.76/19.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.76/19.98  thf('2', plain,
% 19.76/19.98      (![X3 : $i, X4 : $i]:
% 19.76/19.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 19.76/19.98      inference('demod', [status(thm)], ['0', '1'])).
% 19.76/19.98  thf(t70_enumset1, axiom,
% 19.76/19.98    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 19.76/19.98  thf('3', plain,
% 19.76/19.98      (![X8 : $i, X9 : $i]:
% 19.76/19.98         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 19.76/19.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.76/19.98  thf(t71_enumset1, axiom,
% 19.76/19.98    (![A:$i,B:$i,C:$i]:
% 19.76/19.98     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 19.76/19.98  thf('4', plain,
% 19.76/19.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 19.76/19.98         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 19.76/19.98           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 19.76/19.98      inference('cnf', [status(esa)], [t71_enumset1])).
% 19.76/19.98  thf(t72_enumset1, axiom,
% 19.76/19.98    (![A:$i,B:$i,C:$i,D:$i]:
% 19.76/19.98     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 19.76/19.98  thf('5', plain,
% 19.76/19.98      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 19.76/19.98         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 19.76/19.98           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 19.76/19.98      inference('cnf', [status(esa)], [t72_enumset1])).
% 19.76/19.98  thf(d3_enumset1, axiom,
% 19.76/19.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.76/19.98     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 19.76/19.98       ( ![G:$i]:
% 19.76/19.98         ( ( r2_hidden @ G @ F ) <=>
% 19.76/19.98           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 19.76/19.98                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 19.76/19.98  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 19.76/19.98  thf(zf_stmt_1, axiom,
% 19.76/19.98    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 19.76/19.98     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 19.76/19.98       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 19.76/19.98         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 19.76/19.98  thf(zf_stmt_2, axiom,
% 19.76/19.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.76/19.98     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 19.76/19.98       ( ![G:$i]:
% 19.76/19.98         ( ( r2_hidden @ G @ F ) <=>
% 19.76/19.98           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 19.76/19.98  thf('6', plain,
% 19.76/19.98      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 19.76/19.98         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 19.76/19.98          | (r2_hidden @ X29 @ X35)
% 19.76/19.98          | ((X35) != (k3_enumset1 @ X34 @ X33 @ X32 @ X31 @ X30)))),
% 19.76/19.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.76/19.98  thf('7', plain,
% 19.76/19.98      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 19.76/19.98         ((r2_hidden @ X29 @ (k3_enumset1 @ X34 @ X33 @ X32 @ X31 @ X30))
% 19.76/19.98          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 19.76/19.98      inference('simplify', [status(thm)], ['6'])).
% 19.76/19.98  thf('8', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 19.76/19.98         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 19.76/19.98          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 19.76/19.98      inference('sup+', [status(thm)], ['5', '7'])).
% 19.76/19.98  thf('9', plain,
% 19.76/19.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 19.76/19.98         (((X23) != (X24))
% 19.76/19.98          | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X22))),
% 19.76/19.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.76/19.98  thf('10', plain,
% 19.76/19.98      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 19.76/19.98         ~ (zip_tseitin_0 @ X24 @ X24 @ X25 @ X26 @ X27 @ X22)),
% 19.76/19.98      inference('simplify', [status(thm)], ['9'])).
% 19.76/19.98  thf('11', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.76/19.98         (r2_hidden @ X3 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 19.76/19.98      inference('sup-', [status(thm)], ['8', '10'])).
% 19.76/19.98  thf('12', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 19.76/19.98      inference('sup+', [status(thm)], ['4', '11'])).
% 19.76/19.98  thf('13', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 19.76/19.98      inference('sup+', [status(thm)], ['3', '12'])).
% 19.76/19.98  thf(t4_setfam_1, axiom,
% 19.76/19.98    (![A:$i,B:$i]:
% 19.76/19.98     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 19.76/19.98  thf('14', plain,
% 19.76/19.98      (![X43 : $i, X44 : $i]:
% 19.76/19.98         ((r1_tarski @ (k1_setfam_1 @ X43) @ X44) | ~ (r2_hidden @ X44 @ X43))),
% 19.76/19.98      inference('cnf', [status(esa)], [t4_setfam_1])).
% 19.76/19.98  thf('15', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 19.76/19.98      inference('sup-', [status(thm)], ['13', '14'])).
% 19.76/19.98  thf(t19_xboole_1, axiom,
% 19.76/19.98    (![A:$i,B:$i,C:$i]:
% 19.76/19.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 19.76/19.98       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 19.76/19.98  thf('16', plain,
% 19.76/19.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 19.76/19.98         (~ (r1_tarski @ X5 @ X6)
% 19.76/19.98          | ~ (r1_tarski @ X5 @ X7)
% 19.76/19.98          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 19.76/19.98      inference('cnf', [status(esa)], [t19_xboole_1])).
% 19.76/19.98  thf('17', plain,
% 19.76/19.98      (![X38 : $i, X39 : $i]:
% 19.76/19.98         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 19.76/19.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.76/19.98  thf('18', plain,
% 19.76/19.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 19.76/19.98         (~ (r1_tarski @ X5 @ X6)
% 19.76/19.98          | ~ (r1_tarski @ X5 @ X7)
% 19.76/19.98          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 19.76/19.98      inference('demod', [status(thm)], ['16', '17'])).
% 19.76/19.98  thf('19', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 19.76/19.98           (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))
% 19.76/19.98          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2))),
% 19.76/19.98      inference('sup-', [status(thm)], ['15', '18'])).
% 19.76/19.98  thf('20', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 19.76/19.98          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 19.76/19.98      inference('sup-', [status(thm)], ['2', '19'])).
% 19.76/19.98  thf(d10_xboole_0, axiom,
% 19.76/19.98    (![A:$i,B:$i]:
% 19.76/19.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.76/19.98  thf('21', plain,
% 19.76/19.98      (![X0 : $i, X2 : $i]:
% 19.76/19.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.76/19.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.76/19.98  thf('22', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 19.76/19.98             (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 19.76/19.98          | ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 19.76/19.98              = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 19.76/19.98      inference('sup-', [status(thm)], ['20', '21'])).
% 19.76/19.98  thf('23', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 19.76/19.98          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 19.76/19.98      inference('sup-', [status(thm)], ['2', '19'])).
% 19.76/19.98  thf('24', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 19.76/19.98           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 19.76/19.98      inference('demod', [status(thm)], ['22', '23'])).
% 19.76/19.98  thf('25', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 19.76/19.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.76/19.98  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 19.76/19.98      inference('simplify', [status(thm)], ['25'])).
% 19.76/19.98  thf('27', plain,
% 19.76/19.98      (![X3 : $i, X4 : $i]:
% 19.76/19.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 19.76/19.98      inference('demod', [status(thm)], ['0', '1'])).
% 19.76/19.98  thf(t3_subset, axiom,
% 19.76/19.98    (![A:$i,B:$i]:
% 19.76/19.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 19.76/19.98  thf('28', plain,
% 19.76/19.98      (![X40 : $i, X42 : $i]:
% 19.76/19.98         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 19.76/19.98      inference('cnf', [status(esa)], [t3_subset])).
% 19.76/19.98  thf('29', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 19.76/19.98          (k1_zfmisc_1 @ X0))),
% 19.76/19.98      inference('sup-', [status(thm)], ['27', '28'])).
% 19.76/19.98  thf(cc2_relat_1, axiom,
% 19.76/19.98    (![A:$i]:
% 19.76/19.98     ( ( v1_relat_1 @ A ) =>
% 19.76/19.98       ( ![B:$i]:
% 19.76/19.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 19.76/19.98  thf('30', plain,
% 19.76/19.98      (![X45 : $i, X46 : $i]:
% 19.76/19.98         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 19.76/19.98          | (v1_relat_1 @ X45)
% 19.76/19.98          | ~ (v1_relat_1 @ X46))),
% 19.76/19.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.76/19.98  thf('31', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X0)
% 19.76/19.98          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 19.76/19.98      inference('sup-', [status(thm)], ['29', '30'])).
% 19.76/19.98  thf('32', plain,
% 19.76/19.98      (![X3 : $i, X4 : $i]:
% 19.76/19.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 19.76/19.98      inference('demod', [status(thm)], ['0', '1'])).
% 19.76/19.98  thf(t50_relat_1, axiom,
% 19.76/19.98    (![A:$i]:
% 19.76/19.98     ( ( v1_relat_1 @ A ) =>
% 19.76/19.98       ( ![B:$i]:
% 19.76/19.98         ( ( v1_relat_1 @ B ) =>
% 19.76/19.98           ( ![C:$i]:
% 19.76/19.98             ( ( v1_relat_1 @ C ) =>
% 19.76/19.98               ( ![D:$i]:
% 19.76/19.98                 ( ( v1_relat_1 @ D ) =>
% 19.76/19.98                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 19.76/19.98                     ( r1_tarski @
% 19.76/19.98                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 19.76/19.98  thf('33', plain,
% 19.76/19.98      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X47)
% 19.76/19.98          | ~ (v1_relat_1 @ X48)
% 19.76/19.98          | (r1_tarski @ (k5_relat_1 @ X49 @ X50) @ (k5_relat_1 @ X47 @ X48))
% 19.76/19.98          | ~ (r1_tarski @ X50 @ X48)
% 19.76/19.98          | ~ (r1_tarski @ X49 @ X47)
% 19.76/19.98          | ~ (v1_relat_1 @ X50)
% 19.76/19.98          | ~ (v1_relat_1 @ X49))),
% 19.76/19.98      inference('cnf', [status(esa)], [t50_relat_1])).
% 19.76/19.98  thf('34', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X2)
% 19.76/19.98          | ~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 19.76/19.98          | ~ (r1_tarski @ X2 @ X3)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 19.76/19.98             (k5_relat_1 @ X3 @ X0))
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | ~ (v1_relat_1 @ X3))),
% 19.76/19.98      inference('sup-', [status(thm)], ['32', '33'])).
% 19.76/19.98  thf('35', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X1)
% 19.76/19.98          | ~ (v1_relat_1 @ X2)
% 19.76/19.98          | ~ (v1_relat_1 @ X1)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.76/19.98             (k5_relat_1 @ X2 @ X1))
% 19.76/19.98          | ~ (r1_tarski @ X3 @ X2)
% 19.76/19.98          | ~ (v1_relat_1 @ X3))),
% 19.76/19.98      inference('sup-', [status(thm)], ['31', '34'])).
% 19.76/19.98  thf('36', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X3)
% 19.76/19.98          | ~ (r1_tarski @ X3 @ X2)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.76/19.98             (k5_relat_1 @ X2 @ X1))
% 19.76/19.98          | ~ (v1_relat_1 @ X2)
% 19.76/19.98          | ~ (v1_relat_1 @ X1))),
% 19.76/19.98      inference('simplify', [status(thm)], ['35'])).
% 19.76/19.98  thf('37', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X1)
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 19.76/19.98             (k5_relat_1 @ X0 @ X1))
% 19.76/19.98          | ~ (v1_relat_1 @ X0))),
% 19.76/19.98      inference('sup-', [status(thm)], ['26', '36'])).
% 19.76/19.98  thf('38', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         ((r1_tarski @ 
% 19.76/19.98           (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 19.76/19.98           (k5_relat_1 @ X0 @ X1))
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | ~ (v1_relat_1 @ X1))),
% 19.76/19.98      inference('simplify', [status(thm)], ['37'])).
% 19.76/19.98  thf('39', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         ((r1_tarski @ 
% 19.76/19.98           (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.76/19.98           (k5_relat_1 @ X2 @ X0))
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | ~ (v1_relat_1 @ X2))),
% 19.76/19.98      inference('sup+', [status(thm)], ['24', '38'])).
% 19.76/19.98  thf('40', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         ((r1_tarski @ 
% 19.76/19.98           (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 19.76/19.98           (k5_relat_1 @ X0 @ X1))
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | ~ (v1_relat_1 @ X1))),
% 19.76/19.98      inference('simplify', [status(thm)], ['37'])).
% 19.76/19.98  thf('41', plain,
% 19.76/19.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 19.76/19.98         (~ (r1_tarski @ X5 @ X6)
% 19.76/19.98          | ~ (r1_tarski @ X5 @ X7)
% 19.76/19.98          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 19.76/19.98      inference('demod', [status(thm)], ['16', '17'])).
% 19.76/19.98  thf('42', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X0)
% 19.76/19.98          | ~ (v1_relat_1 @ X1)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 19.76/19.98             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 19.76/19.98          | ~ (r1_tarski @ 
% 19.76/19.98               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 19.76/19.98      inference('sup-', [status(thm)], ['40', '41'])).
% 19.76/19.98  thf('43', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X1)
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 19.76/19.98             (k1_setfam_1 @ 
% 19.76/19.98              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 19.76/19.98          | ~ (v1_relat_1 @ X1)
% 19.76/19.98          | ~ (v1_relat_1 @ X2))),
% 19.76/19.98      inference('sup-', [status(thm)], ['39', '42'])).
% 19.76/19.98  thf('44', plain,
% 19.76/19.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.76/19.98         (~ (v1_relat_1 @ X2)
% 19.76/19.98          | (r1_tarski @ 
% 19.76/19.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 19.76/19.98             (k1_setfam_1 @ 
% 19.76/19.98              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 19.76/19.98          | ~ (v1_relat_1 @ X0)
% 19.76/19.98          | ~ (v1_relat_1 @ X1))),
% 19.76/19.98      inference('simplify', [status(thm)], ['43'])).
% 19.76/19.98  thf(t52_relat_1, conjecture,
% 19.76/19.98    (![A:$i]:
% 19.76/19.98     ( ( v1_relat_1 @ A ) =>
% 19.76/19.98       ( ![B:$i]:
% 19.76/19.98         ( ( v1_relat_1 @ B ) =>
% 19.76/19.98           ( ![C:$i]:
% 19.76/19.98             ( ( v1_relat_1 @ C ) =>
% 19.76/19.98               ( r1_tarski @
% 19.76/19.98                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 19.76/19.98                 ( k3_xboole_0 @
% 19.76/19.98                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 19.76/19.98  thf(zf_stmt_3, negated_conjecture,
% 19.76/19.98    (~( ![A:$i]:
% 19.76/19.98        ( ( v1_relat_1 @ A ) =>
% 19.76/19.98          ( ![B:$i]:
% 19.76/19.98            ( ( v1_relat_1 @ B ) =>
% 19.76/19.98              ( ![C:$i]:
% 19.76/19.98                ( ( v1_relat_1 @ C ) =>
% 19.76/19.98                  ( r1_tarski @
% 19.76/19.98                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 19.76/19.98                    ( k3_xboole_0 @
% 19.76/19.98                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 19.76/19.98    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 19.76/19.98  thf('45', plain,
% 19.76/19.98      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 19.76/19.98          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 19.76/19.98           (k5_relat_1 @ sk_A @ sk_C)))),
% 19.76/19.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.76/19.98  thf('46', plain,
% 19.76/19.98      (![X38 : $i, X39 : $i]:
% 19.76/19.98         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 19.76/19.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.76/19.98  thf('47', plain,
% 19.76/19.98      (![X38 : $i, X39 : $i]:
% 19.76/19.98         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 19.76/19.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.76/19.98  thf('48', plain,
% 19.76/19.98      (~ (r1_tarski @ 
% 19.76/19.98          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 19.76/19.98          (k1_setfam_1 @ 
% 19.76/19.98           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 19.76/19.98      inference('demod', [status(thm)], ['45', '46', '47'])).
% 19.76/19.98  thf('49', plain,
% 19.76/19.98      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 19.76/19.98      inference('sup-', [status(thm)], ['44', '48'])).
% 19.76/19.98  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 19.76/19.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.76/19.98  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 19.76/19.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.76/19.98  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 19.76/19.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.76/19.98  thf('53', plain, ($false),
% 19.76/19.98      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 19.76/19.98  
% 19.76/19.98  % SZS output end Refutation
% 19.76/19.98  
% 19.76/19.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
