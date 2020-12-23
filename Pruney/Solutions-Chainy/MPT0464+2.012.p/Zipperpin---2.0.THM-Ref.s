%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ajl2lqUCdK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:10 EST 2020

% Result     : Theorem 10.33s
% Output     : Refutation 10.33s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 171 expanded)
%              Number of leaves         :   34 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  839 (1673 expanded)
%              Number of equality atoms :   34 (  71 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
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

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X30 @ X37 )
      | ( X37
       != ( k4_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X30 @ ( k4_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X23 != X24 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X22 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('16',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X45 ) @ X46 )
      | ~ ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_relat_1 @ X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k5_relat_1 @ X51 @ X52 ) @ ( k5_relat_1 @ X49 @ X50 ) )
      | ~ ( r1_tarski @ X52 @ X50 )
      | ~ ( r1_tarski @ X51 @ X49 )
      | ~ ( v1_relat_1 @ X52 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

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

thf('47',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ajl2lqUCdK
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.33/10.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.33/10.59  % Solved by: fo/fo7.sh
% 10.33/10.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.33/10.59  % done 12133 iterations in 10.130s
% 10.33/10.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.33/10.59  % SZS output start Refutation
% 10.33/10.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.33/10.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.33/10.59  thf(sk_B_type, type, sk_B: $i).
% 10.33/10.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.33/10.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.33/10.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 10.33/10.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.33/10.59  thf(sk_C_type, type, sk_C: $i).
% 10.33/10.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 10.33/10.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 10.33/10.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.33/10.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.33/10.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.33/10.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 10.33/10.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 10.33/10.59  thf(sk_A_type, type, sk_A: $i).
% 10.33/10.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 10.33/10.59  thf(t17_xboole_1, axiom,
% 10.33/10.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 10.33/10.59  thf('0', plain,
% 10.33/10.59      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 10.33/10.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 10.33/10.59  thf(t12_setfam_1, axiom,
% 10.33/10.59    (![A:$i,B:$i]:
% 10.33/10.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 10.33/10.59  thf('1', plain,
% 10.33/10.59      (![X40 : $i, X41 : $i]:
% 10.33/10.59         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 10.33/10.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.33/10.59  thf('2', plain,
% 10.33/10.59      (![X3 : $i, X4 : $i]:
% 10.33/10.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 10.33/10.59      inference('demod', [status(thm)], ['0', '1'])).
% 10.33/10.59  thf(t70_enumset1, axiom,
% 10.33/10.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 10.33/10.59  thf('3', plain,
% 10.33/10.59      (![X8 : $i, X9 : $i]:
% 10.33/10.59         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 10.33/10.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.33/10.59  thf(t71_enumset1, axiom,
% 10.33/10.59    (![A:$i,B:$i,C:$i]:
% 10.33/10.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 10.33/10.59  thf('4', plain,
% 10.33/10.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.33/10.59         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 10.33/10.59           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 10.33/10.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.33/10.59  thf(t72_enumset1, axiom,
% 10.33/10.59    (![A:$i,B:$i,C:$i,D:$i]:
% 10.33/10.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 10.33/10.59  thf('5', plain,
% 10.33/10.59      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 10.33/10.59         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 10.33/10.59           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 10.33/10.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.33/10.59  thf(t73_enumset1, axiom,
% 10.33/10.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 10.33/10.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 10.33/10.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 10.33/10.59  thf('6', plain,
% 10.33/10.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 10.33/10.59         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 10.33/10.59           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 10.33/10.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 10.33/10.59  thf(d4_enumset1, axiom,
% 10.33/10.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 10.33/10.59     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 10.33/10.59       ( ![H:$i]:
% 10.33/10.59         ( ( r2_hidden @ H @ G ) <=>
% 10.33/10.59           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 10.33/10.59                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 10.33/10.59  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 10.33/10.59  thf(zf_stmt_1, axiom,
% 10.33/10.59    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 10.33/10.59     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 10.33/10.59       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 10.33/10.59         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 10.33/10.59  thf(zf_stmt_2, axiom,
% 10.33/10.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 10.33/10.59     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 10.33/10.59       ( ![H:$i]:
% 10.33/10.59         ( ( r2_hidden @ H @ G ) <=>
% 10.33/10.59           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 10.33/10.59  thf('7', plain,
% 10.33/10.59      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 10.33/10.59         X37 : $i]:
% 10.33/10.59         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 10.33/10.59          | (r2_hidden @ X30 @ X37)
% 10.33/10.59          | ((X37) != (k4_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31)))),
% 10.33/10.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.33/10.59  thf('8', plain,
% 10.33/10.59      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 10.33/10.59         ((r2_hidden @ X30 @ (k4_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32 @ X31))
% 10.33/10.59          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 10.33/10.59      inference('simplify', [status(thm)], ['7'])).
% 10.33/10.59  thf('9', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.33/10.59         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 10.33/10.59          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 10.33/10.59      inference('sup+', [status(thm)], ['6', '8'])).
% 10.33/10.59  thf('10', plain,
% 10.33/10.59      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.33/10.59         (((X23) != (X24))
% 10.33/10.59          | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X22))),
% 10.33/10.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.33/10.59  thf('11', plain,
% 10.33/10.59      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.33/10.59         ~ (zip_tseitin_0 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X22)),
% 10.33/10.59      inference('simplify', [status(thm)], ['10'])).
% 10.33/10.59  thf('12', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.33/10.59         (r2_hidden @ X4 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 10.33/10.59      inference('sup-', [status(thm)], ['9', '11'])).
% 10.33/10.59  thf('13', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.33/10.59         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 10.33/10.59      inference('sup+', [status(thm)], ['5', '12'])).
% 10.33/10.59  thf('14', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 10.33/10.59      inference('sup+', [status(thm)], ['4', '13'])).
% 10.33/10.59  thf('15', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 10.33/10.59      inference('sup+', [status(thm)], ['3', '14'])).
% 10.33/10.59  thf(t4_setfam_1, axiom,
% 10.33/10.59    (![A:$i,B:$i]:
% 10.33/10.59     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 10.33/10.59  thf('16', plain,
% 10.33/10.59      (![X45 : $i, X46 : $i]:
% 10.33/10.59         ((r1_tarski @ (k1_setfam_1 @ X45) @ X46) | ~ (r2_hidden @ X46 @ X45))),
% 10.33/10.59      inference('cnf', [status(esa)], [t4_setfam_1])).
% 10.33/10.59  thf('17', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 10.33/10.59      inference('sup-', [status(thm)], ['15', '16'])).
% 10.33/10.59  thf(t19_xboole_1, axiom,
% 10.33/10.59    (![A:$i,B:$i,C:$i]:
% 10.33/10.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 10.33/10.59       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 10.33/10.59  thf('18', plain,
% 10.33/10.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.33/10.59         (~ (r1_tarski @ X5 @ X6)
% 10.33/10.59          | ~ (r1_tarski @ X5 @ X7)
% 10.33/10.59          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 10.33/10.59      inference('cnf', [status(esa)], [t19_xboole_1])).
% 10.33/10.59  thf('19', plain,
% 10.33/10.59      (![X40 : $i, X41 : $i]:
% 10.33/10.59         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 10.33/10.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.33/10.59  thf('20', plain,
% 10.33/10.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.33/10.59         (~ (r1_tarski @ X5 @ X6)
% 10.33/10.59          | ~ (r1_tarski @ X5 @ X7)
% 10.33/10.59          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 10.33/10.59      inference('demod', [status(thm)], ['18', '19'])).
% 10.33/10.59  thf('21', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 10.33/10.59           (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))
% 10.33/10.59          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2))),
% 10.33/10.59      inference('sup-', [status(thm)], ['17', '20'])).
% 10.33/10.59  thf('22', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 10.33/10.59          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 10.33/10.59      inference('sup-', [status(thm)], ['2', '21'])).
% 10.33/10.59  thf(d10_xboole_0, axiom,
% 10.33/10.59    (![A:$i,B:$i]:
% 10.33/10.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.33/10.59  thf('23', plain,
% 10.33/10.59      (![X0 : $i, X2 : $i]:
% 10.33/10.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.33/10.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.33/10.59  thf('24', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 10.33/10.59             (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 10.33/10.59          | ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 10.33/10.59              = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 10.33/10.59      inference('sup-', [status(thm)], ['22', '23'])).
% 10.33/10.59  thf('25', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 10.33/10.59          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 10.33/10.59      inference('sup-', [status(thm)], ['2', '21'])).
% 10.33/10.59  thf('26', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 10.33/10.59           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 10.33/10.59      inference('demod', [status(thm)], ['24', '25'])).
% 10.33/10.59  thf('27', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 10.33/10.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.33/10.59  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.33/10.59      inference('simplify', [status(thm)], ['27'])).
% 10.33/10.59  thf('29', plain,
% 10.33/10.59      (![X3 : $i, X4 : $i]:
% 10.33/10.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 10.33/10.59      inference('demod', [status(thm)], ['0', '1'])).
% 10.33/10.59  thf(t3_subset, axiom,
% 10.33/10.59    (![A:$i,B:$i]:
% 10.33/10.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.33/10.59  thf('30', plain,
% 10.33/10.59      (![X42 : $i, X44 : $i]:
% 10.33/10.59         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 10.33/10.59      inference('cnf', [status(esa)], [t3_subset])).
% 10.33/10.59  thf('31', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 10.33/10.59          (k1_zfmisc_1 @ X0))),
% 10.33/10.59      inference('sup-', [status(thm)], ['29', '30'])).
% 10.33/10.59  thf(cc2_relat_1, axiom,
% 10.33/10.59    (![A:$i]:
% 10.33/10.59     ( ( v1_relat_1 @ A ) =>
% 10.33/10.59       ( ![B:$i]:
% 10.33/10.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.33/10.59  thf('32', plain,
% 10.33/10.59      (![X47 : $i, X48 : $i]:
% 10.33/10.59         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 10.33/10.59          | (v1_relat_1 @ X47)
% 10.33/10.59          | ~ (v1_relat_1 @ X48))),
% 10.33/10.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.33/10.59  thf('33', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X0)
% 10.33/10.59          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 10.33/10.59      inference('sup-', [status(thm)], ['31', '32'])).
% 10.33/10.59  thf('34', plain,
% 10.33/10.59      (![X3 : $i, X4 : $i]:
% 10.33/10.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 10.33/10.59      inference('demod', [status(thm)], ['0', '1'])).
% 10.33/10.59  thf(t50_relat_1, axiom,
% 10.33/10.59    (![A:$i]:
% 10.33/10.59     ( ( v1_relat_1 @ A ) =>
% 10.33/10.59       ( ![B:$i]:
% 10.33/10.59         ( ( v1_relat_1 @ B ) =>
% 10.33/10.59           ( ![C:$i]:
% 10.33/10.59             ( ( v1_relat_1 @ C ) =>
% 10.33/10.59               ( ![D:$i]:
% 10.33/10.59                 ( ( v1_relat_1 @ D ) =>
% 10.33/10.59                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 10.33/10.59                     ( r1_tarski @
% 10.33/10.59                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 10.33/10.59  thf('35', plain,
% 10.33/10.59      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X49)
% 10.33/10.59          | ~ (v1_relat_1 @ X50)
% 10.33/10.59          | (r1_tarski @ (k5_relat_1 @ X51 @ X52) @ (k5_relat_1 @ X49 @ X50))
% 10.33/10.59          | ~ (r1_tarski @ X52 @ X50)
% 10.33/10.59          | ~ (r1_tarski @ X51 @ X49)
% 10.33/10.59          | ~ (v1_relat_1 @ X52)
% 10.33/10.59          | ~ (v1_relat_1 @ X51))),
% 10.33/10.59      inference('cnf', [status(esa)], [t50_relat_1])).
% 10.33/10.59  thf('36', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X2)
% 10.33/10.59          | ~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 10.33/10.59          | ~ (r1_tarski @ X2 @ X3)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 10.33/10.59             (k5_relat_1 @ X3 @ X0))
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | ~ (v1_relat_1 @ X3))),
% 10.33/10.59      inference('sup-', [status(thm)], ['34', '35'])).
% 10.33/10.59  thf('37', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X1)
% 10.33/10.59          | ~ (v1_relat_1 @ X2)
% 10.33/10.59          | ~ (v1_relat_1 @ X1)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 10.33/10.59             (k5_relat_1 @ X2 @ X1))
% 10.33/10.59          | ~ (r1_tarski @ X3 @ X2)
% 10.33/10.59          | ~ (v1_relat_1 @ X3))),
% 10.33/10.59      inference('sup-', [status(thm)], ['33', '36'])).
% 10.33/10.59  thf('38', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X3)
% 10.33/10.59          | ~ (r1_tarski @ X3 @ X2)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 10.33/10.59             (k5_relat_1 @ X2 @ X1))
% 10.33/10.59          | ~ (v1_relat_1 @ X2)
% 10.33/10.59          | ~ (v1_relat_1 @ X1))),
% 10.33/10.59      inference('simplify', [status(thm)], ['37'])).
% 10.33/10.59  thf('39', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X1)
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 10.33/10.59             (k5_relat_1 @ X0 @ X1))
% 10.33/10.59          | ~ (v1_relat_1 @ X0))),
% 10.33/10.59      inference('sup-', [status(thm)], ['28', '38'])).
% 10.33/10.59  thf('40', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         ((r1_tarski @ 
% 10.33/10.59           (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 10.33/10.59           (k5_relat_1 @ X0 @ X1))
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | ~ (v1_relat_1 @ X1))),
% 10.33/10.59      inference('simplify', [status(thm)], ['39'])).
% 10.33/10.59  thf('41', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         ((r1_tarski @ 
% 10.33/10.59           (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 10.33/10.59           (k5_relat_1 @ X2 @ X0))
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | ~ (v1_relat_1 @ X2))),
% 10.33/10.59      inference('sup+', [status(thm)], ['26', '40'])).
% 10.33/10.59  thf('42', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         ((r1_tarski @ 
% 10.33/10.59           (k5_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ 
% 10.33/10.59           (k5_relat_1 @ X0 @ X1))
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | ~ (v1_relat_1 @ X1))),
% 10.33/10.59      inference('simplify', [status(thm)], ['39'])).
% 10.33/10.59  thf('43', plain,
% 10.33/10.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.33/10.59         (~ (r1_tarski @ X5 @ X6)
% 10.33/10.59          | ~ (r1_tarski @ X5 @ X7)
% 10.33/10.59          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 10.33/10.59      inference('demod', [status(thm)], ['18', '19'])).
% 10.33/10.59  thf('44', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X0)
% 10.33/10.59          | ~ (v1_relat_1 @ X1)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 10.33/10.59             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 10.33/10.59          | ~ (r1_tarski @ 
% 10.33/10.59               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 10.33/10.59      inference('sup-', [status(thm)], ['42', '43'])).
% 10.33/10.59  thf('45', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X1)
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 10.33/10.59             (k1_setfam_1 @ 
% 10.33/10.59              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 10.33/10.59          | ~ (v1_relat_1 @ X1)
% 10.33/10.59          | ~ (v1_relat_1 @ X2))),
% 10.33/10.59      inference('sup-', [status(thm)], ['41', '44'])).
% 10.33/10.59  thf('46', plain,
% 10.33/10.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.33/10.59         (~ (v1_relat_1 @ X2)
% 10.33/10.59          | (r1_tarski @ 
% 10.33/10.59             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 10.33/10.59             (k1_setfam_1 @ 
% 10.33/10.59              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 10.33/10.59          | ~ (v1_relat_1 @ X0)
% 10.33/10.59          | ~ (v1_relat_1 @ X1))),
% 10.33/10.59      inference('simplify', [status(thm)], ['45'])).
% 10.33/10.59  thf(t52_relat_1, conjecture,
% 10.33/10.59    (![A:$i]:
% 10.33/10.59     ( ( v1_relat_1 @ A ) =>
% 10.33/10.59       ( ![B:$i]:
% 10.33/10.59         ( ( v1_relat_1 @ B ) =>
% 10.33/10.59           ( ![C:$i]:
% 10.33/10.59             ( ( v1_relat_1 @ C ) =>
% 10.33/10.59               ( r1_tarski @
% 10.33/10.59                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 10.33/10.59                 ( k3_xboole_0 @
% 10.33/10.59                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 10.33/10.59  thf(zf_stmt_3, negated_conjecture,
% 10.33/10.59    (~( ![A:$i]:
% 10.33/10.59        ( ( v1_relat_1 @ A ) =>
% 10.33/10.59          ( ![B:$i]:
% 10.33/10.59            ( ( v1_relat_1 @ B ) =>
% 10.33/10.59              ( ![C:$i]:
% 10.33/10.59                ( ( v1_relat_1 @ C ) =>
% 10.33/10.59                  ( r1_tarski @
% 10.33/10.59                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 10.33/10.59                    ( k3_xboole_0 @
% 10.33/10.59                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 10.33/10.59    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 10.33/10.59  thf('47', plain,
% 10.33/10.59      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 10.33/10.59          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 10.33/10.59           (k5_relat_1 @ sk_A @ sk_C)))),
% 10.33/10.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.33/10.59  thf('48', plain,
% 10.33/10.59      (![X40 : $i, X41 : $i]:
% 10.33/10.59         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 10.33/10.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.33/10.59  thf('49', plain,
% 10.33/10.59      (![X40 : $i, X41 : $i]:
% 10.33/10.59         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 10.33/10.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 10.33/10.59  thf('50', plain,
% 10.33/10.59      (~ (r1_tarski @ 
% 10.33/10.59          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 10.33/10.59          (k1_setfam_1 @ 
% 10.33/10.59           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 10.33/10.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 10.33/10.59  thf('51', plain,
% 10.33/10.59      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 10.33/10.59      inference('sup-', [status(thm)], ['46', '50'])).
% 10.33/10.59  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 10.33/10.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.33/10.59  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 10.33/10.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.33/10.59  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 10.33/10.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.33/10.59  thf('55', plain, ($false),
% 10.33/10.59      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 10.33/10.59  
% 10.33/10.59  % SZS output end Refutation
% 10.33/10.59  
% 10.33/10.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
