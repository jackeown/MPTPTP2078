%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sL8yrcmS9l

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:29 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 262 expanded)
%              Number of leaves         :   40 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  709 (3099 expanded)
%              Number of equality atoms :   37 ( 140 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X5 @ X6 ) @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) @ sk_C ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) @ sk_C ) @ sk_D_1 ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_C
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_C
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
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
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','35'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['24','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','40','43'])).

thf('45',plain,
    ( sk_C
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','44'])).

thf('46',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','40','43'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','40','43'])).

thf('56',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X39 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) )
 != sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sL8yrcmS9l
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:54:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 219 iterations in 0.223s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.48/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.66  thf(t17_funct_2, conjecture,
% 0.48/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.48/0.66            ( ![E:$i]:
% 0.48/0.66              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.48/0.66               ( ![E:$i]:
% 0.48/0.66                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.48/0.66                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.48/0.66  thf('0', plain,
% 0.48/0.66      ((r2_hidden @ sk_C @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.66         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.48/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('4', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf(t146_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.48/0.66  thf('5', plain,
% 0.48/0.66      (![X8 : $i]:
% 0.48/0.66         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 0.48/0.66          | ~ (v1_relat_1 @ X8))),
% 0.48/0.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.48/0.66  thf(t143_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ C ) =>
% 0.48/0.66       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.48/0.66         ( ?[D:$i]:
% 0.48/0.66           ( ( r2_hidden @ D @ B ) & 
% 0.48/0.66             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.48/0.66             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.48/0.66          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X5 @ X6) @ X6) @ X7)
% 0.48/0.66          | ~ (v1_relat_1 @ X7))),
% 0.48/0.66      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | (r2_hidden @ 
% 0.48/0.66             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((r2_hidden @ 
% 0.48/0.66           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.48/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66        | (r2_hidden @ 
% 0.48/0.66           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C) @ sk_C) @ 
% 0.48/0.66           sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['4', '8'])).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(cc1_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( v1_relat_1 @ C ) ))).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.66         ((v1_relat_1 @ X19)
% 0.48/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.48/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.66  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      ((r2_hidden @ 
% 0.48/0.66        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C) @ sk_C) @ 
% 0.48/0.66        sk_D_1)),
% 0.48/0.66      inference('demod', [status(thm)], ['9', '12'])).
% 0.48/0.66  thf(t8_funct_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.66       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.48/0.66         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.48/0.66           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.48/0.66         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.48/0.66          | ((X16) = (k1_funct_1 @ X15 @ X14))
% 0.48/0.66          | ~ (v1_funct_1 @ X15)
% 0.48/0.66          | ~ (v1_relat_1 @ X15))),
% 0.48/0.66      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.66        | ((sk_C)
% 0.48/0.66            = (k1_funct_1 @ sk_D_1 @ 
% 0.48/0.66               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.66  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.66  thf('17', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (((sk_C)
% 0.48/0.66         = (k1_funct_1 @ sk_D_1 @ 
% 0.48/0.66            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C)))),
% 0.48/0.66      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.48/0.66  thf('19', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d1_funct_2, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_1, axiom,
% 0.48/0.66    (![C:$i,B:$i,A:$i]:
% 0.48/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.48/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.48/0.66         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.48/0.66          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.48/0.66          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.48/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_4, axiom,
% 0.48/0.66    (![B:$i,A:$i]:
% 0.48/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.48/0.66  thf(zf_stmt_5, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.48/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.66         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.48/0.66          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.48/0.66          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.48/0.66        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.66  thf('25', plain,
% 0.48/0.66      (![X31 : $i, X32 : $i]:
% 0.48/0.66         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.48/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.66  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.66  thf('27', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.48/0.66      inference('sup+', [status(thm)], ['25', '26'])).
% 0.48/0.66  thf('28', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf('29', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(dt_k2_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.66         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.48/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.48/0.66  thf('31', plain,
% 0.48/0.66      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) @ 
% 0.48/0.66        (k1_zfmisc_1 @ sk_B_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('32', plain,
% 0.48/0.66      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('33', plain,
% 0.48/0.66      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.66  thf(l3_subset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X1 @ X2)
% 0.48/0.66          | (r2_hidden @ X1 @ X3)
% 0.48/0.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.48/0.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((r2_hidden @ X0 @ sk_B_1)
% 0.48/0.66          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.66  thf('36', plain, ((r2_hidden @ sk_C @ sk_B_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['28', '35'])).
% 0.48/0.66  thf(t7_ordinal1, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (![X17 : $i, X18 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.48/0.66      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.48/0.66  thf('38', plain, (~ (r1_tarski @ sk_B_1 @ sk_C)),
% 0.48/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.66  thf('39', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.48/0.66      inference('sup-', [status(thm)], ['27', '38'])).
% 0.48/0.66  thf('40', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)),
% 0.48/0.66      inference('demod', [status(thm)], ['24', '39'])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.66  thf('42', plain,
% 0.48/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.48/0.66         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.48/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.66  thf('43', plain,
% 0.48/0.66      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.66  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['21', '40', '43'])).
% 0.48/0.66  thf('45', plain,
% 0.48/0.66      (((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C)))),
% 0.48/0.66      inference('demod', [status(thm)], ['18', '44'])).
% 0.48/0.66  thf('46', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf('47', plain,
% 0.48/0.66      (![X8 : $i]:
% 0.48/0.66         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 0.48/0.66          | ~ (v1_relat_1 @ X8))),
% 0.48/0.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.48/0.66  thf('48', plain,
% 0.48/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.48/0.66          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ (k1_relat_1 @ X7))
% 0.48/0.66          | ~ (v1_relat_1 @ X7))),
% 0.48/0.66      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.48/0.66  thf('49', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.48/0.66             (k1_relat_1 @ X0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.66  thf('50', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.48/0.66      inference('simplify', [status(thm)], ['49'])).
% 0.48/0.66  thf('51', plain,
% 0.48/0.66      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C) @ 
% 0.48/0.66           (k1_relat_1 @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['46', '50'])).
% 0.48/0.66  thf('52', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.66  thf('53', plain,
% 0.48/0.66      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C) @ 
% 0.48/0.66        (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['51', '52'])).
% 0.48/0.66  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['21', '40', '43'])).
% 0.48/0.66  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['21', '40', '43'])).
% 0.48/0.66  thf('56', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_A)),
% 0.48/0.66      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.48/0.66  thf('57', plain,
% 0.48/0.66      (![X39 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X39 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X39) != (sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('58', plain,
% 0.48/0.66      (((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C)) != (sk_C))),
% 0.48/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.66  thf('59', plain, ($false),
% 0.48/0.66      inference('simplify_reflect-', [status(thm)], ['45', '58'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
