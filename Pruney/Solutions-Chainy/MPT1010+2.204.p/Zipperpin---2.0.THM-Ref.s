%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PBwrmnyY8M

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 114 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  817 (1115 expanded)
%              Number of equality atoms :   74 (  98 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

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

thf(zf_stmt_0,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 )
      | ( X16 = X20 )
      | ( X16 = X21 )
      | ( X16 = X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('27',plain,(
    ! [X35: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X33: $i] :
      ( ( ( k10_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X34: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X35: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k2_relat_1 @ X38 ) )
      | ( ( k10_relat_1 @ X38 @ ( k1_tarski @ X39 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_tarski @ X1 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_tarski @ X1 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X23 @ X30 )
      | ( X30
       != ( k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X23 @ ( k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X15: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X19 @ X20 @ X21 @ X15 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PBwrmnyY8M
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:20:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 115 iterations in 0.062s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(d4_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.21/0.52       ( ![H:$i]:
% 0.21/0.52         ( ( r2_hidden @ H @ G ) <=>
% 0.21/0.52           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.21/0.52                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, axiom,
% 0.21/0.52    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.21/0.52       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.21/0.52         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.52          | ((X16) = (X17))
% 0.21/0.52          | ((X16) = (X18))
% 0.21/0.52          | ((X16) = (X19))
% 0.21/0.52          | ((X16) = (X20))
% 0.21/0.52          | ((X16) = (X21))
% 0.21/0.52          | ((X16) = (X22)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t65_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.52         ( m1_subset_1 @
% 0.21/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.52       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.52            ( m1_subset_1 @
% 0.21/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.52          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.52  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf(t7_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X40 @ X41)
% 0.21/0.52          | ((X42) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ X43)
% 0.21/0.52          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.21/0.52          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('9', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf(t70_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf(t71_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.52  thf(t72_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.52           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.52  thf(t73_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.52           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.52  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.21/0.52       ( ![H:$i]:
% 0.21/0.52         ( ( r2_hidden @ H @ G ) <=>
% 0.21/0.52           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.21/0.52         X31 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X31 @ X30)
% 0.21/0.52          | ~ (zip_tseitin_0 @ X31 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.21/0.52          | ((X30) != (k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.21/0.52         (~ (zip_tseitin_0 @ X31 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.21/0.52          | ~ (r2_hidden @ X31 @ 
% 0.21/0.52               (k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.52        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.21/0.52             sk_B @ sk_B @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.52        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.52  thf('24', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('25', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf(t71_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.52  thf('27', plain, (![X35 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(t169_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X33 : $i]:
% 0.21/0.52         (((k10_relat_1 @ X33 @ (k2_relat_1 @ X33)) = (k1_relat_1 @ X33))
% 0.21/0.52          | ~ (v1_relat_1 @ X33))),
% 0.21/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.21/0.52            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain, (![X34 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(fc3_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('31', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.52  thf('33', plain, (![X35 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(t142_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.52         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X38 : $i, X39 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X39 @ (k2_relat_1 @ X38))
% 0.21/0.52          | ((k10_relat_1 @ X38 @ (k1_tarski @ X39)) != (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_tarski @ X1))
% 0.21/0.52              != (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.52          | ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_tarski @ X1))
% 0.21/0.52              != (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 0.21/0.52          | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.21/0.52           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.52           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 0.21/0.52         X30 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.21/0.52          | (r2_hidden @ X23 @ X30)
% 0.21/0.52          | ((X30) != (k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.52         ((r2_hidden @ X23 @ (k4_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 @ X24))
% 0.21/0.52          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.21/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.52          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.21/0.52      inference('sup+', [status(thm)], ['43', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         (((X16) != (X15))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X15 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X19 @ X20 @ X21 @ X15)),
% 0.21/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['42', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['41', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['40', '51'])).
% 0.21/0.52  thf('53', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '52'])).
% 0.21/0.52  thf('54', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '53'])).
% 0.21/0.52  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
