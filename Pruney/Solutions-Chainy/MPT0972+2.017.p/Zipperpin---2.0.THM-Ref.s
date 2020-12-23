%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O4pJsh3zmL

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:35 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 465 expanded)
%              Number of leaves         :   40 ( 159 expanded)
%              Depth                    :   27
%              Number of atoms          : 1060 (5864 expanded)
%              Number of equality atoms :   90 ( 247 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(rc1_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X7 ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( X0 = sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( sk_D = sk_C_2 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_D = sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_D = sk_C_2 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( sk_D = sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_D = sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['27'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_D = sk_C_2 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( sk_D = sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( sk_D = sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('55',plain,
    ( ( sk_D = sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_D = sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_D = sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,
    ( ( sk_A != sk_A )
    | ( sk_D = sk_C_2 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D = sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_A != sk_A )
    | ( sk_D = sk_C_2 )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D = sk_C_2 ) ),
    inference(demod,[status(thm)],['63','66','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D = sk_C_2 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_D = sk_C_2 )
    | ( sk_D = sk_C_2 ) ),
    inference('sup+',[status(thm)],['53','69'])).

thf('71',plain,
    ( ( sk_D = sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X34: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X34 )
        = ( k1_funct_1 @ sk_D @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_D = sk_C_2 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['73'])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_funct_1 @ X12 @ ( sk_C_1 @ X11 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 @ X12 ) ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('78',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('81',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_A )
    | ( sk_D = sk_C_2 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['40','82'])).

thf('84',plain,
    ( ( sk_D = sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( sk_D = sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('86',plain,(
    sk_D = sk_C_2 ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('88',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O4pJsh3zmL
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:15:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.91/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.17  % Solved by: fo/fo7.sh
% 0.91/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.17  % done 715 iterations in 0.721s
% 0.91/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.17  % SZS output start Refutation
% 0.91/1.17  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.17  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.91/1.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.17  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.17  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.91/1.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.91/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.17  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.17  thf(t18_funct_2, conjecture,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.17       ( ![D:$i]:
% 0.91/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.17           ( ( ![E:$i]:
% 0.91/1.17               ( ( r2_hidden @ E @ A ) =>
% 0.91/1.17                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.91/1.17             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.91/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.17          ( ![D:$i]:
% 0.91/1.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.17              ( ( ![E:$i]:
% 0.91/1.17                  ( ( r2_hidden @ E @ A ) =>
% 0.91/1.17                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.91/1.17                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 0.91/1.17    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 0.91/1.17  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf(d3_tarski, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.91/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.91/1.17  thf('1', plain,
% 0.91/1.17      (![X1 : $i, X3 : $i]:
% 0.91/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.17  thf(d1_funct_2, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.17  thf(zf_stmt_1, axiom,
% 0.91/1.17    (![B:$i,A:$i]:
% 0.91/1.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.17       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.17  thf('2', plain,
% 0.91/1.17      (![X26 : $i, X27 : $i]:
% 0.91/1.17         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.17  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.17  thf('4', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.17      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.17  thf(rc1_subset_1, axiom,
% 0.91/1.17    (![A:$i]:
% 0.91/1.17     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.17       ( ?[B:$i]:
% 0.91/1.17         ( ( ~( v1_xboole_0 @ B ) ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ))).
% 0.91/1.17  thf('5', plain,
% 0.91/1.17      (![X7 : $i]:
% 0.91/1.17         ((m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7)) | (v1_xboole_0 @ X7))),
% 0.91/1.17      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.91/1.17  thf(cc4_relset_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( v1_xboole_0 @ A ) =>
% 0.91/1.17       ( ![C:$i]:
% 0.91/1.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.91/1.17           ( v1_xboole_0 @ C ) ) ) ))).
% 0.91/1.17  thf('6', plain,
% 0.91/1.17      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.17         (~ (v1_xboole_0 @ X16)
% 0.91/1.17          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.91/1.17          | (v1_xboole_0 @ X17))),
% 0.91/1.17      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.91/1.17  thf('7', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.91/1.17          | (v1_xboole_0 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.91/1.17          | ~ (v1_xboole_0 @ X0))),
% 0.91/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 0.91/1.17  thf('8', plain,
% 0.91/1.17      (![X7 : $i]: (~ (v1_xboole_0 @ (sk_B @ X7)) | (v1_xboole_0 @ X7))),
% 0.91/1.17      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.91/1.17  thf('9', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.91/1.17      inference('clc', [status(thm)], ['7', '8'])).
% 0.91/1.17  thf('10', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf(t5_subset, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.91/1.17          ( v1_xboole_0 @ C ) ) ))).
% 0.91/1.17  thf('11', plain,
% 0.91/1.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.17         (~ (r2_hidden @ X8 @ X9)
% 0.91/1.17          | ~ (v1_xboole_0 @ X10)
% 0.91/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t5_subset])).
% 0.91/1.17  thf('12', plain,
% 0.91/1.17      (![X0 : $i]:
% 0.91/1.17         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.91/1.17          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.91/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.17  thf('13', plain,
% 0.91/1.17      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.91/1.17      inference('sup-', [status(thm)], ['9', '12'])).
% 0.91/1.17  thf('14', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.91/1.17      inference('sup-', [status(thm)], ['4', '13'])).
% 0.91/1.17  thf('15', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((r1_tarski @ sk_D @ X0) | (zip_tseitin_0 @ sk_B_1 @ X1))),
% 0.91/1.17      inference('sup-', [status(thm)], ['1', '14'])).
% 0.91/1.17  thf('16', plain,
% 0.91/1.17      (![X1 : $i, X3 : $i]:
% 0.91/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.17  thf('17', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.17      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.17  thf('18', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.91/1.17      inference('clc', [status(thm)], ['7', '8'])).
% 0.91/1.17  thf('19', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('20', plain,
% 0.91/1.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.17         (~ (r2_hidden @ X8 @ X9)
% 0.91/1.17          | ~ (v1_xboole_0 @ X10)
% 0.91/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t5_subset])).
% 0.91/1.17  thf('21', plain,
% 0.91/1.17      (![X0 : $i]:
% 0.91/1.17         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.91/1.17          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.91/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.17  thf('22', plain,
% 0.91/1.17      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.91/1.17      inference('sup-', [status(thm)], ['18', '21'])).
% 0.91/1.17  thf('23', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.91/1.17      inference('sup-', [status(thm)], ['17', '22'])).
% 0.91/1.17  thf('24', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_0 @ sk_B_1 @ X1))),
% 0.91/1.17      inference('sup-', [status(thm)], ['16', '23'])).
% 0.91/1.17  thf(d10_xboole_0, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.17  thf('25', plain,
% 0.91/1.17      (![X4 : $i, X6 : $i]:
% 0.91/1.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.91/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.17  thf('26', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 0.91/1.17          | ~ (r1_tarski @ X0 @ sk_C_2)
% 0.91/1.17          | ((X0) = (sk_C_2)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.17  thf('27', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 0.91/1.17          | ((sk_D) = (sk_C_2))
% 0.91/1.17          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.91/1.17      inference('sup-', [status(thm)], ['15', '26'])).
% 0.91/1.17  thf('28', plain,
% 0.91/1.17      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_D) = (sk_C_2)))),
% 0.91/1.17      inference('condensation', [status(thm)], ['27'])).
% 0.91/1.17  thf('29', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.17  thf(zf_stmt_3, axiom,
% 0.91/1.17    (![C:$i,B:$i,A:$i]:
% 0.91/1.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.17  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.17  thf(zf_stmt_5, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.17  thf('30', plain,
% 0.91/1.17      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.17         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.91/1.17          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.91/1.17          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.17  thf('31', plain,
% 0.91/1.17      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.17        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.91/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.17  thf('32', plain,
% 0.91/1.17      ((((sk_D) = (sk_C_2)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.91/1.17      inference('sup-', [status(thm)], ['28', '31'])).
% 0.91/1.17  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('34', plain,
% 0.91/1.17      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.17         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.91/1.17          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.91/1.17          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.17  thf('35', plain,
% 0.91/1.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.17  thf('36', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.17  thf('37', plain,
% 0.91/1.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.17         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.91/1.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.17  thf('38', plain,
% 0.91/1.17      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.91/1.17      inference('sup-', [status(thm)], ['36', '37'])).
% 0.91/1.17  thf('39', plain,
% 0.91/1.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.17        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.17      inference('demod', [status(thm)], ['35', '38'])).
% 0.91/1.17  thf('40', plain, ((((sk_D) = (sk_C_2)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['32', '39'])).
% 0.91/1.17  thf('41', plain,
% 0.91/1.17      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_D) = (sk_C_2)))),
% 0.91/1.17      inference('condensation', [status(thm)], ['27'])).
% 0.91/1.17  thf('42', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('43', plain,
% 0.91/1.17      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.17         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.91/1.17          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.91/1.17          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.17  thf('44', plain,
% 0.91/1.17      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.91/1.17        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.91/1.17      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.17  thf('45', plain,
% 0.91/1.17      ((((sk_D) = (sk_C_2)) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 0.91/1.17      inference('sup-', [status(thm)], ['41', '44'])).
% 0.91/1.17  thf('46', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('47', plain,
% 0.91/1.17      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.17         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.91/1.17          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.91/1.17          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.17  thf('48', plain,
% 0.91/1.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.91/1.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.17  thf('49', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('50', plain,
% 0.91/1.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.17         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.91/1.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.17  thf('51', plain,
% 0.91/1.17      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.91/1.17      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.17  thf('52', plain,
% 0.91/1.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.91/1.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.91/1.17      inference('demod', [status(thm)], ['48', '51'])).
% 0.91/1.17  thf('53', plain, ((((sk_D) = (sk_C_2)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['45', '52'])).
% 0.91/1.17  thf('54', plain, ((((sk_D) = (sk_C_2)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['32', '39'])).
% 0.91/1.17  thf('55', plain, ((((sk_D) = (sk_C_2)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['45', '52'])).
% 0.91/1.17  thf(t9_funct_1, axiom,
% 0.91/1.17    (![A:$i]:
% 0.91/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.17       ( ![B:$i]:
% 0.91/1.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.17           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.91/1.17               ( ![C:$i]:
% 0.91/1.17                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.91/1.17                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.91/1.17             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.91/1.17  thf('56', plain,
% 0.91/1.17      (![X11 : $i, X12 : $i]:
% 0.91/1.17         (~ (v1_relat_1 @ X11)
% 0.91/1.17          | ~ (v1_funct_1 @ X11)
% 0.91/1.17          | ((X12) = (X11))
% 0.91/1.17          | (r2_hidden @ (sk_C_1 @ X11 @ X12) @ (k1_relat_1 @ X12))
% 0.91/1.17          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.91/1.17          | ~ (v1_funct_1 @ X12)
% 0.91/1.17          | ~ (v1_relat_1 @ X12))),
% 0.91/1.17      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.91/1.17  thf('57', plain,
% 0.91/1.17      (![X0 : $i]:
% 0.91/1.17         (((sk_A) != (k1_relat_1 @ X0))
% 0.91/1.17          | ((sk_D) = (sk_C_2))
% 0.91/1.17          | ~ (v1_relat_1 @ sk_C_2)
% 0.91/1.17          | ~ (v1_funct_1 @ sk_C_2)
% 0.91/1.17          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.91/1.17          | ((sk_C_2) = (X0))
% 0.91/1.17          | ~ (v1_funct_1 @ X0)
% 0.91/1.17          | ~ (v1_relat_1 @ X0))),
% 0.91/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.91/1.17  thf('58', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf(cc1_relset_1, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.17       ( v1_relat_1 @ C ) ))).
% 0.91/1.17  thf('59', plain,
% 0.91/1.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.17         ((v1_relat_1 @ X13)
% 0.91/1.17          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.91/1.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.17  thf('60', plain, ((v1_relat_1 @ sk_C_2)),
% 0.91/1.17      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.17  thf('61', plain, ((v1_funct_1 @ sk_C_2)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('62', plain,
% 0.91/1.17      (![X0 : $i]:
% 0.91/1.17         (((sk_A) != (k1_relat_1 @ X0))
% 0.91/1.17          | ((sk_D) = (sk_C_2))
% 0.91/1.17          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.91/1.17          | ((sk_C_2) = (X0))
% 0.91/1.17          | ~ (v1_funct_1 @ X0)
% 0.91/1.17          | ~ (v1_relat_1 @ X0))),
% 0.91/1.17      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.91/1.17  thf('63', plain,
% 0.91/1.17      ((((sk_A) != (sk_A))
% 0.91/1.17        | ((sk_D) = (sk_C_2))
% 0.91/1.17        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.17        | ((sk_C_2) = (sk_D))
% 0.91/1.17        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.91/1.17        | ((sk_D) = (sk_C_2)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['54', '62'])).
% 0.91/1.17  thf('64', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('65', plain,
% 0.91/1.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.17         ((v1_relat_1 @ X13)
% 0.91/1.17          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.91/1.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.17  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.17      inference('sup-', [status(thm)], ['64', '65'])).
% 0.91/1.17  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('68', plain,
% 0.91/1.17      ((((sk_A) != (sk_A))
% 0.91/1.17        | ((sk_D) = (sk_C_2))
% 0.91/1.17        | ((sk_C_2) = (sk_D))
% 0.91/1.17        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.91/1.17        | ((sk_D) = (sk_C_2)))),
% 0.91/1.17      inference('demod', [status(thm)], ['63', '66', '67'])).
% 0.91/1.17  thf('69', plain,
% 0.91/1.17      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.91/1.17        | ((sk_D) = (sk_C_2)))),
% 0.91/1.17      inference('simplify', [status(thm)], ['68'])).
% 0.91/1.17  thf('70', plain,
% 0.91/1.17      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 0.91/1.17        | ((sk_D) = (sk_C_2))
% 0.91/1.17        | ((sk_D) = (sk_C_2)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['53', '69'])).
% 0.91/1.17  thf('71', plain,
% 0.91/1.17      ((((sk_D) = (sk_C_2)) | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 0.91/1.17      inference('simplify', [status(thm)], ['70'])).
% 0.91/1.17  thf('72', plain,
% 0.91/1.17      (![X34 : $i]:
% 0.91/1.17         (((k1_funct_1 @ sk_C_2 @ X34) = (k1_funct_1 @ sk_D @ X34))
% 0.91/1.17          | ~ (r2_hidden @ X34 @ sk_A))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('73', plain,
% 0.91/1.17      ((((sk_D) = (sk_C_2))
% 0.91/1.17        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 0.91/1.17            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 0.91/1.17      inference('sup-', [status(thm)], ['71', '72'])).
% 0.91/1.17  thf('74', plain,
% 0.91/1.17      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 0.91/1.17         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 0.91/1.17      inference('condensation', [status(thm)], ['73'])).
% 0.91/1.17  thf('75', plain,
% 0.91/1.17      (![X11 : $i, X12 : $i]:
% 0.91/1.17         (~ (v1_relat_1 @ X11)
% 0.91/1.17          | ~ (v1_funct_1 @ X11)
% 0.91/1.17          | ((X12) = (X11))
% 0.91/1.17          | ((k1_funct_1 @ X12 @ (sk_C_1 @ X11 @ X12))
% 0.91/1.17              != (k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ X12)))
% 0.91/1.17          | ((k1_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.91/1.17          | ~ (v1_funct_1 @ X12)
% 0.91/1.17          | ~ (v1_relat_1 @ X12))),
% 0.91/1.17      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.91/1.17  thf('76', plain,
% 0.91/1.17      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 0.91/1.17          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 0.91/1.17        | ~ (v1_relat_1 @ sk_C_2)
% 0.91/1.17        | ~ (v1_funct_1 @ sk_C_2)
% 0.91/1.17        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 0.91/1.17        | ((sk_C_2) = (sk_D))
% 0.91/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.17        | ~ (v1_relat_1 @ sk_D))),
% 0.91/1.17      inference('sup-', [status(thm)], ['74', '75'])).
% 0.91/1.17  thf('77', plain, ((v1_relat_1 @ sk_C_2)),
% 0.91/1.17      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.17  thf('78', plain, ((v1_funct_1 @ sk_C_2)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.17      inference('sup-', [status(thm)], ['64', '65'])).
% 0.91/1.17  thf('81', plain,
% 0.91/1.17      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 0.91/1.17          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 0.91/1.17        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 0.91/1.17        | ((sk_C_2) = (sk_D)))),
% 0.91/1.17      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.91/1.17  thf('82', plain,
% 0.91/1.17      ((((sk_C_2) = (sk_D)) | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D)))),
% 0.91/1.17      inference('simplify', [status(thm)], ['81'])).
% 0.91/1.17  thf('83', plain,
% 0.91/1.17      ((((k1_relat_1 @ sk_C_2) != (sk_A))
% 0.91/1.17        | ((sk_D) = (sk_C_2))
% 0.91/1.17        | ((sk_C_2) = (sk_D)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['40', '82'])).
% 0.91/1.17  thf('84', plain, ((((sk_D) = (sk_C_2)) | ((k1_relat_1 @ sk_C_2) != (sk_A)))),
% 0.91/1.17      inference('simplify', [status(thm)], ['83'])).
% 0.91/1.17  thf('85', plain, ((((sk_D) = (sk_C_2)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['45', '52'])).
% 0.91/1.17  thf('86', plain, (((sk_D) = (sk_C_2))),
% 0.91/1.17      inference('clc', [status(thm)], ['84', '85'])).
% 0.91/1.17  thf('87', plain,
% 0.91/1.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf(redefinition_r2_relset_1, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.91/1.17  thf('88', plain,
% 0.91/1.17      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.91/1.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.91/1.17          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 0.91/1.17          | ((X22) != (X25)))),
% 0.91/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.91/1.17  thf('89', plain,
% 0.91/1.17      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.17         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 0.91/1.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.91/1.17      inference('simplify', [status(thm)], ['88'])).
% 0.91/1.17  thf('90', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 0.91/1.17      inference('sup-', [status(thm)], ['87', '89'])).
% 0.91/1.17  thf('91', plain, ($false),
% 0.91/1.17      inference('demod', [status(thm)], ['0', '86', '90'])).
% 0.91/1.17  
% 0.91/1.17  % SZS output end Refutation
% 0.91/1.17  
% 1.01/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
