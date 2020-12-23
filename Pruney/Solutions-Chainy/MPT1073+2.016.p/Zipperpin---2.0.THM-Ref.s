%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vIKooezBnj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:15 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 267 expanded)
%              Number of leaves         :   43 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  720 (3064 expanded)
%              Number of equality atoms :   36 ( 131 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['9','12'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X12 )
      | ( X13
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
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

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['30','35'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['24','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','40','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','44'])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X4 @ X5 ) @ X4 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('55',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','40','43'])).

thf('57',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','40','43'])).

thf('58',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X36: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vIKooezBnj
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 122 iterations in 0.128s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.58  thf(t190_funct_2, conjecture,
% 0.37/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.37/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.37/0.58       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.37/0.58            ( ![E:$i]:
% 0.37/0.58              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.37/0.58            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.37/0.58          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.37/0.58               ( ![E:$i]:
% 0.37/0.58                 ( ( m1_subset_1 @ E @ B ) =>
% 0.37/0.58                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.37/0.58  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.58         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.37/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.58  thf(t146_relat_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X7 : $i]:
% 0.37/0.58         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.37/0.58          | ~ (v1_relat_1 @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.37/0.58  thf(t143_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ C ) =>
% 0.37/0.58       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.37/0.58         ( ?[D:$i]:
% 0.37/0.58           ( ( r2_hidden @ D @ B ) & 
% 0.37/0.58             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.37/0.58             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X5 @ (k9_relat_1 @ X6 @ X4))
% 0.37/0.58          | (r2_hidden @ (k4_tarski @ (sk_D @ X6 @ X4 @ X5) @ X5) @ X6)
% 0.37/0.58          | ~ (v1_relat_1 @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ 
% 0.37/0.58           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      ((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.58        | (r2_hidden @ 
% 0.37/0.58           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.37/0.58           sk_D_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '8'])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(cc1_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( v1_relat_1 @ C ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.58         ((v1_relat_1 @ X16)
% 0.37/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.58  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      ((r2_hidden @ 
% 0.37/0.58        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.37/0.58        sk_D_1)),
% 0.37/0.58      inference('demod', [status(thm)], ['9', '12'])).
% 0.37/0.58  thf(t8_funct_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.58       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.58         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.58           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.58         (~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ X12)
% 0.37/0.58          | ((X13) = (k1_funct_1 @ X12 @ X11))
% 0.37/0.58          | ~ (v1_funct_1 @ X12)
% 0.37/0.58          | ~ (v1_relat_1 @ X12))),
% 0.37/0.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      ((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.58        | ~ (v1_funct_1 @ sk_D_1)
% 0.37/0.58        | ((sk_A)
% 0.37/0.58            = (k1_funct_1 @ sk_D_1 @ 
% 0.37/0.58               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('17', plain, ((v1_funct_1 @ sk_D_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (((sk_A)
% 0.37/0.58         = (k1_funct_1 @ sk_D_1 @ 
% 0.37/0.58            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.37/0.58  thf('19', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d1_funct_2, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_1, axiom,
% 0.37/0.58    (![C:$i,B:$i,A:$i]:
% 0.37/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.58         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.37/0.58          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.37/0.58          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.37/0.58        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.58  thf(zf_stmt_4, axiom,
% 0.37/0.58    (![B:$i,A:$i]:
% 0.37/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.58  thf(zf_stmt_5, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.58         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.37/0.58          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.37/0.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.37/0.58        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X28 : $i, X29 : $i]:
% 0.37/0.58         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.58  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.37/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(cc2_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.58         ((v5_relat_1 @ X19 @ X21)
% 0.37/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.58  thf('30', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 0.37/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.58  thf('31', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.58  thf(t202_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.37/0.58       ( ![C:$i]:
% 0.37/0.58         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.37/0.58          | (r2_hidden @ X8 @ X10)
% 0.37/0.58          | ~ (v5_relat_1 @ X9 @ X10)
% 0.37/0.58          | ~ (v1_relat_1 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ sk_D_1)
% 0.37/0.58          | ~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.37/0.58          | (r2_hidden @ sk_A @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.58  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_1 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '35'])).
% 0.37/0.58  thf(t7_ordinal1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.58  thf('38', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.37/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('39', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['27', '38'])).
% 0.37/0.58  thf('40', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.37/0.58      inference('demod', [status(thm)], ['24', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.58         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.37/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.58  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['21', '40', '43'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['18', '44'])).
% 0.37/0.58  thf('46', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X7 : $i]:
% 0.37/0.58         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.37/0.58          | ~ (v1_relat_1 @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X5 @ (k9_relat_1 @ X6 @ X4))
% 0.37/0.58          | (r2_hidden @ (sk_D @ X6 @ X4 @ X5) @ X4)
% 0.37/0.58          | ~ (v1_relat_1 @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.37/0.58             (k1_relat_1 @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      ((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.58        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.37/0.58           (k1_relat_1 @ sk_D_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['46', '50'])).
% 0.37/0.58  thf('52', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.37/0.58        (k1_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.58  thf(t1_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.37/0.58        (k1_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.58  thf('56', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['21', '40', '43'])).
% 0.37/0.58  thf('57', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['21', '40', '43'])).
% 0.37/0.58  thf('58', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.58      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      (![X36 : $i]:
% 0.37/0.58         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X36))
% 0.37/0.58          | ~ (m1_subset_1 @ X36 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.58  thf('61', plain, ($false),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['45', '60'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
