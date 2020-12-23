%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4AG59H2eE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 200 expanded)
%              Number of leaves         :   54 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  816 (2030 expanded)
%              Number of equality atoms :   63 ( 129 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( v1_funct_2 @ X69 @ X67 @ X68 )
      | ( X67
        = ( k1_relset_1 @ X67 @ X68 @ X69 ) )
      | ~ ( zip_tseitin_1 @ X69 @ X68 @ X67 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X65: $i,X66: $i] :
      ( ( zip_tseitin_0 @ X65 @ X66 )
      | ( X65 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( zip_tseitin_0 @ X70 @ X71 )
      | ( zip_tseitin_1 @ X72 @ X70 @ X71 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X71 @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relset_1 @ X51 @ X52 @ X50 )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(fc4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc4_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('24',plain,(
    ! [X57: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X57 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( r2_hidden @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('33',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k1_mcart_1 @ X54 )
        = X53 )
      | ( ( k1_mcart_1 @ X54 )
        = X55 )
      | ~ ( r2_hidden @ X54 @ ( k2_zfmisc_1 @ ( k2_tarski @ X55 @ X53 ) @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_mcart_1 @ X2 )
        = X0 )
      | ( ( k1_mcart_1 @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_mcart_1 @ X2 )
        = X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) )
      | ( ( k1_mcart_1 @ X1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X57: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X57 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t91_mcart_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) )
            & ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ( r2_hidden @ ( k1_mcart_1 @ X63 ) @ ( k1_relat_1 @ X64 ) )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t91_mcart_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('47',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X43 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X42 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('48',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v5_relat_1 @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('55',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v5_relat_1 @ X40 @ X41 )
      | ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['61','62'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['23','63','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4AG59H2eE
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:07:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 156 iterations in 0.115s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(t61_funct_2, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.56         ( m1_subset_1 @
% 0.20/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.56            ( m1_subset_1 @
% 0.20/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.20/0.56  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d1_funct_2, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, axiom,
% 0.20/0.56    (![C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.20/0.56         (~ (v1_funct_2 @ X69 @ X67 @ X68)
% 0.20/0.56          | ((X67) = (k1_relset_1 @ X67 @ X68 @ X69))
% 0.20/0.56          | ~ (zip_tseitin_1 @ X69 @ X68 @ X67))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.20/0.56        | ((k1_tarski @ sk_A)
% 0.20/0.56            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf(zf_stmt_2, axiom,
% 0.20/0.56    (![B:$i,A:$i]:
% 0.20/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X65 : $i, X66 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X65 @ X66) | ((X65) = (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_5, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.20/0.56         (~ (zip_tseitin_0 @ X70 @ X71)
% 0.20/0.56          | (zip_tseitin_1 @ X72 @ X70 @ X71)
% 0.20/0.56          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X71 @ X70))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.20/0.56        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.56        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.56  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.20/0.56         (((k1_relset_1 @ X51 @ X52 @ X50) = (k1_relat_1 @ X50))
% 0.20/0.56          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.56         = (k1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.56  thf(t70_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf(t71_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.56  thf(t72_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.56           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.56  thf(fc4_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.56     ( ~( v1_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.56         ~ (v1_xboole_0 @ (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc4_subset_1])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.56  thf('22', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.56  thf('23', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '22'])).
% 0.20/0.56  thf(t6_mcart_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.56                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.56                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.20/0.56                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.20/0.56                       ( r2_hidden @ G @ B ) ) =>
% 0.20/0.56                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X57 : $i]:
% 0.20/0.56         (((X57) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X57) @ X57))),
% 0.20/0.56      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(l3_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X37 @ X38)
% 0.20/0.56          | (r2_hidden @ X37 @ X39)
% 0.20/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.20/0.56           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.56  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.20/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.56  thf('32', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(t15_mcart_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.20/0.56       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.20/0.56         (((k1_mcart_1 @ X54) = (X53))
% 0.20/0.56          | ((k1_mcart_1 @ X54) = (X55))
% 0.20/0.56          | ~ (r2_hidden @ X54 @ (k2_zfmisc_1 @ (k2_tarski @ X55 @ X53) @ X56)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1))
% 0.20/0.56          | ((k1_mcart_1 @ X2) = (X0))
% 0.20/0.56          | ((k1_mcart_1 @ X2) = (X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (((k1_mcart_1 @ X2) = (X0))
% 0.20/0.56          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ X0))
% 0.20/0.56          | ((k1_mcart_1 @ X1) = (sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['31', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C_1)) = (sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X57 : $i]:
% 0.20/0.56         (((X57) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X57) @ X57))),
% 0.20/0.56      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.20/0.56  thf(t91_mcart_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( r2_hidden @ B @ A ) =>
% 0.20/0.56           ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.56             ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X63 : $i, X64 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X63 @ X64)
% 0.20/0.56          | (r2_hidden @ (k1_mcart_1 @ X63) @ (k1_relat_1 @ X64))
% 0.20/0.56          | ~ (v1_relat_1 @ X64))),
% 0.20/0.56      inference('cnf', [status(esa)], [t91_mcart_1])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((X0) = (k1_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ X0)) @ (k1_relat_1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.20/0.56        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['37', '40'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( v1_relat_1 @ C ) ))).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.56         ((v1_relat_1 @ X44)
% 0.20/0.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.56  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.20/0.56        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.56  thf(t12_funct_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.56         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X42 : $i, X43 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X42 @ (k1_relat_1 @ X43))
% 0.20/0.56          | (r2_hidden @ (k1_funct_1 @ X43 @ X42) @ (k2_relat_1 @ X43))
% 0.20/0.56          | ~ (v1_funct_1 @ X43)
% 0.20/0.56          | ~ (v1_relat_1 @ X43))),
% 0.20/0.56      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_C_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc2_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.56         ((v5_relat_1 @ X47 @ X49)
% 0.20/0.56          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.56  thf('54', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf(d19_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) =>
% 0.20/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (![X40 : $i, X41 : $i]:
% 0.20/0.56         (~ (v5_relat_1 @ X40 @ X41)
% 0.20/0.56          | (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 0.20/0.56          | ~ (v1_relat_1 @ X40))),
% 0.20/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.56  thf('57', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf(d3_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.56          | (r2_hidden @ X0 @ X2)
% 0.20/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ sk_B_1)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['51', '60'])).
% 0.20/0.56  thf('62', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('63', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.56  thf(t60_relat_1, axiom,
% 0.20/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.56  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.56  thf('66', plain, ($false),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '63', '64', '65'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
