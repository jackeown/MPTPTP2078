%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iF3bUCDrs2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:38 EST 2020

% Result     : Theorem 7.84s
% Output     : Refutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  143 (1233 expanded)
%              Number of leaves         :   38 ( 372 expanded)
%              Depth                    :   27
%              Number of atoms          : 1136 (21626 expanded)
%              Number of equality atoms :  115 (1220 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

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

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X34: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X34 )
        = ( k1_funct_1 @ sk_D @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( ( k1_funct_1 @ X13 @ ( sk_C_1 @ X12 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_C_1 @ X12 @ X13 ) ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['13','55'])).

thf('57',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('67',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( sk_C @ X0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_2 @ X0 ) ),
    inference(demod,[status(thm)],['74','75','77','78'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('80',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('81',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['67','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('92',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('93',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('95',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','64'])).

thf('98',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('101',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('102',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['96','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iF3bUCDrs2
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.84/8.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.84/8.03  % Solved by: fo/fo7.sh
% 7.84/8.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.84/8.03  % done 5018 iterations in 7.575s
% 7.84/8.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.84/8.03  % SZS output start Refutation
% 7.84/8.03  thf(sk_D_type, type, sk_D: $i).
% 7.84/8.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.84/8.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.84/8.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.84/8.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.84/8.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 7.84/8.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.84/8.03  thf(sk_B_type, type, sk_B: $i).
% 7.84/8.03  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.84/8.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.84/8.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.84/8.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.84/8.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.84/8.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.84/8.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.84/8.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.84/8.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.84/8.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 7.84/8.03  thf(sk_A_type, type, sk_A: $i).
% 7.84/8.03  thf(sk_C_2_type, type, sk_C_2: $i).
% 7.84/8.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.84/8.03  thf(t18_funct_2, conjecture,
% 7.84/8.03    (![A:$i,B:$i,C:$i]:
% 7.84/8.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.84/8.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.84/8.03       ( ![D:$i]:
% 7.84/8.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.84/8.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.84/8.03           ( ( ![E:$i]:
% 7.84/8.03               ( ( r2_hidden @ E @ A ) =>
% 7.84/8.03                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 7.84/8.03             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 7.84/8.03  thf(zf_stmt_0, negated_conjecture,
% 7.84/8.03    (~( ![A:$i,B:$i,C:$i]:
% 7.84/8.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.84/8.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.84/8.03          ( ![D:$i]:
% 7.84/8.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.84/8.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.84/8.03              ( ( ![E:$i]:
% 7.84/8.03                  ( ( r2_hidden @ E @ A ) =>
% 7.84/8.03                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 7.84/8.03                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 7.84/8.03    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 7.84/8.03  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf(d1_funct_2, axiom,
% 7.84/8.03    (![A:$i,B:$i,C:$i]:
% 7.84/8.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.84/8.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.84/8.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.84/8.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.84/8.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.84/8.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.84/8.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.84/8.03  thf(zf_stmt_1, axiom,
% 7.84/8.03    (![B:$i,A:$i]:
% 7.84/8.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.84/8.03       ( zip_tseitin_0 @ B @ A ) ))).
% 7.84/8.03  thf('1', plain,
% 7.84/8.03      (![X26 : $i, X27 : $i]:
% 7.84/8.03         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.84/8.03  thf('2', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.84/8.03  thf(zf_stmt_3, axiom,
% 7.84/8.03    (![C:$i,B:$i,A:$i]:
% 7.84/8.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.84/8.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.84/8.03  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 7.84/8.03  thf(zf_stmt_5, axiom,
% 7.84/8.03    (![A:$i,B:$i,C:$i]:
% 7.84/8.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.84/8.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.84/8.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.84/8.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.84/8.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.84/8.03  thf('3', plain,
% 7.84/8.03      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.84/8.03         (~ (zip_tseitin_0 @ X31 @ X32)
% 7.84/8.03          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 7.84/8.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.84/8.03  thf('4', plain,
% 7.84/8.03      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.84/8.03      inference('sup-', [status(thm)], ['2', '3'])).
% 7.84/8.03  thf('5', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 7.84/8.03      inference('sup-', [status(thm)], ['1', '4'])).
% 7.84/8.03  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('7', plain,
% 7.84/8.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.84/8.03         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 7.84/8.03          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 7.84/8.03          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.84/8.03  thf('8', plain,
% 7.84/8.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 7.84/8.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['6', '7'])).
% 7.84/8.03  thf('9', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf(redefinition_k1_relset_1, axiom,
% 7.84/8.03    (![A:$i,B:$i,C:$i]:
% 7.84/8.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.84/8.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.84/8.03  thf('10', plain,
% 7.84/8.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.84/8.03         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 7.84/8.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 7.84/8.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.84/8.03  thf('11', plain,
% 7.84/8.03      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 7.84/8.03      inference('sup-', [status(thm)], ['9', '10'])).
% 7.84/8.03  thf('12', plain,
% 7.84/8.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 7.84/8.03      inference('demod', [status(thm)], ['8', '11'])).
% 7.84/8.03  thf('13', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['5', '12'])).
% 7.84/8.03  thf('14', plain,
% 7.84/8.03      (![X26 : $i, X27 : $i]:
% 7.84/8.03         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.84/8.03  thf('15', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('16', plain,
% 7.84/8.03      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.84/8.03         (~ (zip_tseitin_0 @ X31 @ X32)
% 7.84/8.03          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 7.84/8.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.84/8.03  thf('17', plain,
% 7.84/8.03      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.84/8.03        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.84/8.03      inference('sup-', [status(thm)], ['15', '16'])).
% 7.84/8.03  thf('18', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 7.84/8.03      inference('sup-', [status(thm)], ['14', '17'])).
% 7.84/8.03  thf('19', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('20', plain,
% 7.84/8.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.84/8.03         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 7.84/8.03          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 7.84/8.03          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.84/8.03  thf('21', plain,
% 7.84/8.03      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.84/8.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['19', '20'])).
% 7.84/8.03  thf('22', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('23', plain,
% 7.84/8.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.84/8.03         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 7.84/8.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 7.84/8.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.84/8.03  thf('24', plain,
% 7.84/8.03      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 7.84/8.03      inference('sup-', [status(thm)], ['22', '23'])).
% 7.84/8.03  thf('25', plain,
% 7.84/8.03      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.84/8.03        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.84/8.03      inference('demod', [status(thm)], ['21', '24'])).
% 7.84/8.03  thf('26', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['18', '25'])).
% 7.84/8.03  thf('27', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['5', '12'])).
% 7.84/8.03  thf('28', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['18', '25'])).
% 7.84/8.03  thf(t9_funct_1, axiom,
% 7.84/8.03    (![A:$i]:
% 7.84/8.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.84/8.03       ( ![B:$i]:
% 7.84/8.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 7.84/8.03           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 7.84/8.03               ( ![C:$i]:
% 7.84/8.03                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 7.84/8.03                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 7.84/8.03             ( ( A ) = ( B ) ) ) ) ) ))).
% 7.84/8.03  thf('29', plain,
% 7.84/8.03      (![X12 : $i, X13 : $i]:
% 7.84/8.03         (~ (v1_relat_1 @ X12)
% 7.84/8.03          | ~ (v1_funct_1 @ X12)
% 7.84/8.03          | ((X13) = (X12))
% 7.84/8.03          | (r2_hidden @ (sk_C_1 @ X12 @ X13) @ (k1_relat_1 @ X13))
% 7.84/8.03          | ((k1_relat_1 @ X13) != (k1_relat_1 @ X12))
% 7.84/8.03          | ~ (v1_funct_1 @ X13)
% 7.84/8.03          | ~ (v1_relat_1 @ X13))),
% 7.84/8.03      inference('cnf', [status(esa)], [t9_funct_1])).
% 7.84/8.03  thf('30', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         (((sk_A) != (k1_relat_1 @ X0))
% 7.84/8.03          | ((sk_B) = (k1_xboole_0))
% 7.84/8.03          | ~ (v1_relat_1 @ sk_C_2)
% 7.84/8.03          | ~ (v1_funct_1 @ sk_C_2)
% 7.84/8.03          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 7.84/8.03          | ((sk_C_2) = (X0))
% 7.84/8.03          | ~ (v1_funct_1 @ X0)
% 7.84/8.03          | ~ (v1_relat_1 @ X0))),
% 7.84/8.03      inference('sup-', [status(thm)], ['28', '29'])).
% 7.84/8.03  thf('31', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf(cc1_relset_1, axiom,
% 7.84/8.03    (![A:$i,B:$i,C:$i]:
% 7.84/8.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.84/8.03       ( v1_relat_1 @ C ) ))).
% 7.84/8.03  thf('32', plain,
% 7.84/8.03      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.84/8.03         ((v1_relat_1 @ X16)
% 7.84/8.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 7.84/8.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.84/8.03  thf('33', plain, ((v1_relat_1 @ sk_C_2)),
% 7.84/8.03      inference('sup-', [status(thm)], ['31', '32'])).
% 7.84/8.03  thf('34', plain, ((v1_funct_1 @ sk_C_2)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('35', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         (((sk_A) != (k1_relat_1 @ X0))
% 7.84/8.03          | ((sk_B) = (k1_xboole_0))
% 7.84/8.03          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 7.84/8.03          | ((sk_C_2) = (X0))
% 7.84/8.03          | ~ (v1_funct_1 @ X0)
% 7.84/8.03          | ~ (v1_relat_1 @ X0))),
% 7.84/8.03      inference('demod', [status(thm)], ['30', '33', '34'])).
% 7.84/8.03  thf('36', plain,
% 7.84/8.03      ((((sk_A) != (sk_A))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ~ (v1_relat_1 @ sk_D)
% 7.84/8.03        | ~ (v1_funct_1 @ sk_D)
% 7.84/8.03        | ((sk_C_2) = (sk_D))
% 7.84/8.03        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['27', '35'])).
% 7.84/8.03  thf('37', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('38', plain,
% 7.84/8.03      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.84/8.03         ((v1_relat_1 @ X16)
% 7.84/8.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 7.84/8.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.84/8.03  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 7.84/8.03      inference('sup-', [status(thm)], ['37', '38'])).
% 7.84/8.03  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('41', plain,
% 7.84/8.03      ((((sk_A) != (sk_A))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((sk_C_2) = (sk_D))
% 7.84/8.03        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0)))),
% 7.84/8.03      inference('demod', [status(thm)], ['36', '39', '40'])).
% 7.84/8.03  thf('42', plain,
% 7.84/8.03      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 7.84/8.03        | ((sk_C_2) = (sk_D))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0)))),
% 7.84/8.03      inference('simplify', [status(thm)], ['41'])).
% 7.84/8.03  thf('43', plain,
% 7.84/8.03      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((sk_C_2) = (sk_D)))),
% 7.84/8.03      inference('sup+', [status(thm)], ['26', '42'])).
% 7.84/8.03  thf('44', plain,
% 7.84/8.03      ((((sk_C_2) = (sk_D))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 7.84/8.03      inference('simplify', [status(thm)], ['43'])).
% 7.84/8.03  thf('45', plain,
% 7.84/8.03      (![X34 : $i]:
% 7.84/8.03         (((k1_funct_1 @ sk_C_2 @ X34) = (k1_funct_1 @ sk_D @ X34))
% 7.84/8.03          | ~ (r2_hidden @ X34 @ sk_A))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('46', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((sk_C_2) = (sk_D))
% 7.84/8.03        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 7.84/8.03            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 7.84/8.03      inference('sup-', [status(thm)], ['44', '45'])).
% 7.84/8.03  thf('47', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 7.84/8.03            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 7.84/8.03      inference('condensation', [status(thm)], ['46'])).
% 7.84/8.03  thf('48', plain,
% 7.84/8.03      (![X12 : $i, X13 : $i]:
% 7.84/8.03         (~ (v1_relat_1 @ X12)
% 7.84/8.03          | ~ (v1_funct_1 @ X12)
% 7.84/8.03          | ((X13) = (X12))
% 7.84/8.03          | ((k1_funct_1 @ X13 @ (sk_C_1 @ X12 @ X13))
% 7.84/8.03              != (k1_funct_1 @ X12 @ (sk_C_1 @ X12 @ X13)))
% 7.84/8.03          | ((k1_relat_1 @ X13) != (k1_relat_1 @ X12))
% 7.84/8.03          | ~ (v1_funct_1 @ X13)
% 7.84/8.03          | ~ (v1_relat_1 @ X13))),
% 7.84/8.03      inference('cnf', [status(esa)], [t9_funct_1])).
% 7.84/8.03  thf('49', plain,
% 7.84/8.03      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 7.84/8.03          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ~ (v1_relat_1 @ sk_C_2)
% 7.84/8.03        | ~ (v1_funct_1 @ sk_C_2)
% 7.84/8.03        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 7.84/8.03        | ((sk_C_2) = (sk_D))
% 7.84/8.03        | ~ (v1_funct_1 @ sk_D)
% 7.84/8.03        | ~ (v1_relat_1 @ sk_D))),
% 7.84/8.03      inference('sup-', [status(thm)], ['47', '48'])).
% 7.84/8.03  thf('50', plain, ((v1_relat_1 @ sk_C_2)),
% 7.84/8.03      inference('sup-', [status(thm)], ['31', '32'])).
% 7.84/8.03  thf('51', plain, ((v1_funct_1 @ sk_C_2)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 7.84/8.03      inference('sup-', [status(thm)], ['37', '38'])).
% 7.84/8.03  thf('54', plain,
% 7.84/8.03      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 7.84/8.03          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 7.84/8.03        | ((sk_C_2) = (sk_D)))),
% 7.84/8.03      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 7.84/8.03  thf('55', plain,
% 7.84/8.03      ((((sk_C_2) = (sk_D))
% 7.84/8.03        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0)))),
% 7.84/8.03      inference('simplify', [status(thm)], ['54'])).
% 7.84/8.03  thf('56', plain,
% 7.84/8.03      ((((k1_relat_1 @ sk_C_2) != (sk_A))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((sk_C_2) = (sk_D)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['13', '55'])).
% 7.84/8.03  thf('57', plain,
% 7.84/8.03      ((((sk_C_2) = (sk_D))
% 7.84/8.03        | ((sk_B) = (k1_xboole_0))
% 7.84/8.03        | ((k1_relat_1 @ sk_C_2) != (sk_A)))),
% 7.84/8.03      inference('simplify', [status(thm)], ['56'])).
% 7.84/8.03  thf('58', plain,
% 7.84/8.03      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['18', '25'])).
% 7.84/8.03  thf('59', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 7.84/8.03      inference('clc', [status(thm)], ['57', '58'])).
% 7.84/8.03  thf('60', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('61', plain,
% 7.84/8.03      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)
% 7.84/8.03        | ((sk_B) = (k1_xboole_0)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['59', '60'])).
% 7.84/8.03  thf('62', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf(redefinition_r2_relset_1, axiom,
% 7.84/8.03    (![A:$i,B:$i,C:$i,D:$i]:
% 7.84/8.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.84/8.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.84/8.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 7.84/8.03  thf('63', plain,
% 7.84/8.03      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.84/8.03         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 7.84/8.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 7.84/8.03          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 7.84/8.03          | ((X22) != (X25)))),
% 7.84/8.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 7.84/8.03  thf('64', plain,
% 7.84/8.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.84/8.03         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 7.84/8.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 7.84/8.03      inference('simplify', [status(thm)], ['63'])).
% 7.84/8.03  thf('65', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 7.84/8.03      inference('sup-', [status(thm)], ['62', '64'])).
% 7.84/8.03  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 7.84/8.03      inference('demod', [status(thm)], ['61', '65'])).
% 7.84/8.03  thf('67', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 7.84/8.03      inference('demod', [status(thm)], ['0', '66'])).
% 7.84/8.03  thf(d3_tarski, axiom,
% 7.84/8.03    (![A:$i,B:$i]:
% 7.84/8.03     ( ( r1_tarski @ A @ B ) <=>
% 7.84/8.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.84/8.03  thf('68', plain,
% 7.84/8.03      (![X1 : $i, X3 : $i]:
% 7.84/8.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.84/8.03      inference('cnf', [status(esa)], [d3_tarski])).
% 7.84/8.03  thf('69', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf(l3_subset_1, axiom,
% 7.84/8.03    (![A:$i,B:$i]:
% 7.84/8.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.84/8.03       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 7.84/8.03  thf('70', plain,
% 7.84/8.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 7.84/8.03         (~ (r2_hidden @ X9 @ X10)
% 7.84/8.03          | (r2_hidden @ X9 @ X11)
% 7.84/8.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 7.84/8.03      inference('cnf', [status(esa)], [l3_subset_1])).
% 7.84/8.03  thf('71', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 7.84/8.03          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 7.84/8.03      inference('sup-', [status(thm)], ['69', '70'])).
% 7.84/8.03  thf('72', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         ((r1_tarski @ sk_C_2 @ X0)
% 7.84/8.03          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['68', '71'])).
% 7.84/8.03  thf(t7_ordinal1, axiom,
% 7.84/8.03    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.84/8.03  thf('73', plain,
% 7.84/8.03      (![X14 : $i, X15 : $i]:
% 7.84/8.03         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 7.84/8.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.84/8.03  thf('74', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         ((r1_tarski @ sk_C_2 @ X0)
% 7.84/8.03          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (sk_C @ X0 @ sk_C_2)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['72', '73'])).
% 7.84/8.03  thf('75', plain, (((sk_B) = (k1_xboole_0))),
% 7.84/8.03      inference('demod', [status(thm)], ['61', '65'])).
% 7.84/8.03  thf(t113_zfmisc_1, axiom,
% 7.84/8.03    (![A:$i,B:$i]:
% 7.84/8.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 7.84/8.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 7.84/8.03  thf('76', plain,
% 7.84/8.03      (![X7 : $i, X8 : $i]:
% 7.84/8.03         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 7.84/8.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 7.84/8.03  thf('77', plain,
% 7.84/8.03      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 7.84/8.03      inference('simplify', [status(thm)], ['76'])).
% 7.84/8.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.84/8.03  thf('78', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 7.84/8.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.84/8.03  thf('79', plain, (![X0 : $i]: (r1_tarski @ sk_C_2 @ X0)),
% 7.84/8.03      inference('demod', [status(thm)], ['74', '75', '77', '78'])).
% 7.84/8.03  thf(t3_xboole_1, axiom,
% 7.84/8.03    (![A:$i]:
% 7.84/8.03     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 7.84/8.03  thf('80', plain,
% 7.84/8.03      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 7.84/8.03      inference('cnf', [status(esa)], [t3_xboole_1])).
% 7.84/8.03  thf('81', plain, (((sk_C_2) = (k1_xboole_0))),
% 7.84/8.03      inference('sup-', [status(thm)], ['79', '80'])).
% 7.84/8.03  thf('82', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D)),
% 7.84/8.03      inference('demod', [status(thm)], ['67', '81'])).
% 7.84/8.03  thf('83', plain,
% 7.84/8.03      (![X1 : $i, X3 : $i]:
% 7.84/8.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.84/8.03      inference('cnf', [status(esa)], [d3_tarski])).
% 7.84/8.03  thf('84', plain,
% 7.84/8.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.84/8.03  thf('85', plain,
% 7.84/8.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 7.84/8.03         (~ (r2_hidden @ X9 @ X10)
% 7.84/8.03          | (r2_hidden @ X9 @ X11)
% 7.84/8.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 7.84/8.03      inference('cnf', [status(esa)], [l3_subset_1])).
% 7.84/8.03  thf('86', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 7.84/8.03          | ~ (r2_hidden @ X0 @ sk_D))),
% 7.84/8.03      inference('sup-', [status(thm)], ['84', '85'])).
% 7.84/8.03  thf('87', plain,
% 7.84/8.03      (![X0 : $i]:
% 7.84/8.03         ((r1_tarski @ sk_D @ X0)
% 7.84/8.03          | (r2_hidden @ (sk_C @ X0 @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['83', '86'])).
% 7.84/8.03  thf('88', plain,
% 7.84/8.03      (![X1 : $i, X3 : $i]:
% 7.84/8.03         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.84/8.03      inference('cnf', [status(esa)], [d3_tarski])).
% 7.84/8.03  thf('89', plain,
% 7.84/8.03      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 7.84/8.03        | (r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.84/8.03      inference('sup-', [status(thm)], ['87', '88'])).
% 7.84/8.03  thf('90', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 7.84/8.03      inference('simplify', [status(thm)], ['89'])).
% 7.84/8.03  thf('91', plain, (((sk_B) = (k1_xboole_0))),
% 7.84/8.03      inference('demod', [status(thm)], ['61', '65'])).
% 7.84/8.03  thf('92', plain,
% 7.84/8.03      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 7.84/8.03      inference('simplify', [status(thm)], ['76'])).
% 7.84/8.03  thf('93', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 7.84/8.03      inference('demod', [status(thm)], ['90', '91', '92'])).
% 7.84/8.03  thf('94', plain,
% 7.84/8.03      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 7.84/8.03      inference('cnf', [status(esa)], [t3_xboole_1])).
% 7.84/8.03  thf('95', plain, (((sk_D) = (k1_xboole_0))),
% 7.84/8.03      inference('sup-', [status(thm)], ['93', '94'])).
% 7.84/8.03  thf('96', plain,
% 7.84/8.03      (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 7.84/8.03      inference('demod', [status(thm)], ['82', '95'])).
% 7.84/8.03  thf('97', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 7.84/8.03      inference('sup-', [status(thm)], ['62', '64'])).
% 7.84/8.03  thf('98', plain, (((sk_B) = (k1_xboole_0))),
% 7.84/8.03      inference('demod', [status(thm)], ['61', '65'])).
% 7.84/8.03  thf('99', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 7.84/8.03      inference('demod', [status(thm)], ['97', '98'])).
% 7.84/8.03  thf('100', plain, (((sk_C_2) = (k1_xboole_0))),
% 7.84/8.03      inference('sup-', [status(thm)], ['79', '80'])).
% 7.84/8.03  thf('101', plain, (((sk_C_2) = (k1_xboole_0))),
% 7.84/8.03      inference('sup-', [status(thm)], ['79', '80'])).
% 7.84/8.03  thf('102', plain,
% 7.84/8.03      ((r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 7.84/8.03      inference('demod', [status(thm)], ['99', '100', '101'])).
% 7.84/8.03  thf('103', plain, ($false), inference('demod', [status(thm)], ['96', '102'])).
% 7.84/8.03  
% 7.84/8.03  % SZS output end Refutation
% 7.84/8.03  
% 7.84/8.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
