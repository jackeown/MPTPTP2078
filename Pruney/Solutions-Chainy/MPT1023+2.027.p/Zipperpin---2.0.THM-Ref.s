%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r8pYEogFQf

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:32 EST 2020

% Result     : Theorem 10.54s
% Output     : Refutation 10.54s
% Verified   : 
% Statistics : Number of formulae       :  142 (1241 expanded)
%              Number of leaves         :   39 ( 376 expanded)
%              Depth                    :   29
%              Number of atoms          : 1095 (21624 expanded)
%              Number of equality atoms :  117 (1232 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
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
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X33: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X33 )
        = ( k1_funct_1 @ sk_D @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C_1 @ X13 @ X14 ) )
       != ( k1_funct_1 @ X13 @ ( sk_C_1 @ X13 @ X14 ) ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('51',plain,
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
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('53',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['13','57'])).

thf('59',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('65',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','67'])).

thf('69',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','68'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','67'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['73','74','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('80',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('81',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','67'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('93',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','93'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['64','66'])).

thf('96',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','67'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('99',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('100',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['94','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r8pYEogFQf
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.54/10.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.54/10.79  % Solved by: fo/fo7.sh
% 10.54/10.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.54/10.79  % done 7319 iterations in 10.350s
% 10.54/10.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.54/10.79  % SZS output start Refutation
% 10.54/10.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.54/10.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.54/10.79  thf(sk_D_type, type, sk_D: $i).
% 10.54/10.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.54/10.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.54/10.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.54/10.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.54/10.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.54/10.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.54/10.79  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.54/10.79  thf(sk_B_type, type, sk_B: $i).
% 10.54/10.79  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 10.54/10.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.54/10.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.54/10.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.54/10.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.54/10.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.54/10.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.54/10.79  thf(sk_A_type, type, sk_A: $i).
% 10.54/10.79  thf(sk_C_2_type, type, sk_C_2: $i).
% 10.54/10.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.54/10.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.54/10.79  thf(t113_funct_2, conjecture,
% 10.54/10.79    (![A:$i,B:$i,C:$i]:
% 10.54/10.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.54/10.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.54/10.79       ( ![D:$i]:
% 10.54/10.79         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.54/10.79             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.54/10.79           ( ( ![E:$i]:
% 10.54/10.79               ( ( m1_subset_1 @ E @ A ) =>
% 10.54/10.79                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 10.54/10.79             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 10.54/10.79  thf(zf_stmt_0, negated_conjecture,
% 10.54/10.79    (~( ![A:$i,B:$i,C:$i]:
% 10.54/10.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.54/10.79            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.54/10.79          ( ![D:$i]:
% 10.54/10.79            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.54/10.79                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.54/10.79              ( ( ![E:$i]:
% 10.54/10.79                  ( ( m1_subset_1 @ E @ A ) =>
% 10.54/10.79                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 10.54/10.79                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 10.54/10.79    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 10.54/10.79  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf(d1_funct_2, axiom,
% 10.54/10.79    (![A:$i,B:$i,C:$i]:
% 10.54/10.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.54/10.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.54/10.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.54/10.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.54/10.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.54/10.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.54/10.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.54/10.79  thf(zf_stmt_1, axiom,
% 10.54/10.79    (![B:$i,A:$i]:
% 10.54/10.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.54/10.79       ( zip_tseitin_0 @ B @ A ) ))).
% 10.54/10.79  thf('1', plain,
% 10.54/10.79      (![X25 : $i, X26 : $i]:
% 10.54/10.79         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.54/10.79  thf('2', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.54/10.79  thf(zf_stmt_3, axiom,
% 10.54/10.79    (![C:$i,B:$i,A:$i]:
% 10.54/10.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.54/10.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.54/10.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.54/10.79  thf(zf_stmt_5, axiom,
% 10.54/10.79    (![A:$i,B:$i,C:$i]:
% 10.54/10.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.54/10.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.54/10.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.54/10.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.54/10.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.54/10.79  thf('3', plain,
% 10.54/10.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 10.54/10.79         (~ (zip_tseitin_0 @ X30 @ X31)
% 10.54/10.79          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 10.54/10.79          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.54/10.79  thf('4', plain,
% 10.54/10.79      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.54/10.79      inference('sup-', [status(thm)], ['2', '3'])).
% 10.54/10.79  thf('5', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 10.54/10.79      inference('sup-', [status(thm)], ['1', '4'])).
% 10.54/10.79  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('7', plain,
% 10.54/10.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.54/10.79         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 10.54/10.79          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 10.54/10.79          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.54/10.79  thf('8', plain,
% 10.54/10.79      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 10.54/10.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['6', '7'])).
% 10.54/10.79  thf('9', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf(redefinition_k1_relset_1, axiom,
% 10.54/10.79    (![A:$i,B:$i,C:$i]:
% 10.54/10.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.54/10.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.54/10.79  thf('10', plain,
% 10.54/10.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 10.54/10.79         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 10.54/10.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 10.54/10.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.54/10.79  thf('11', plain,
% 10.54/10.79      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 10.54/10.79      inference('sup-', [status(thm)], ['9', '10'])).
% 10.54/10.79  thf('12', plain,
% 10.54/10.79      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.54/10.79      inference('demod', [status(thm)], ['8', '11'])).
% 10.54/10.79  thf('13', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['5', '12'])).
% 10.54/10.79  thf('14', plain,
% 10.54/10.79      (![X25 : $i, X26 : $i]:
% 10.54/10.79         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.54/10.79  thf('15', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('16', plain,
% 10.54/10.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 10.54/10.79         (~ (zip_tseitin_0 @ X30 @ X31)
% 10.54/10.79          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 10.54/10.79          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.54/10.79  thf('17', plain,
% 10.54/10.79      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 10.54/10.79        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.54/10.79      inference('sup-', [status(thm)], ['15', '16'])).
% 10.54/10.79  thf('18', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 10.54/10.79      inference('sup-', [status(thm)], ['14', '17'])).
% 10.54/10.79  thf('19', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('20', plain,
% 10.54/10.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.54/10.79         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 10.54/10.79          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 10.54/10.79          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.54/10.79  thf('21', plain,
% 10.54/10.79      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 10.54/10.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['19', '20'])).
% 10.54/10.79  thf('22', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('23', plain,
% 10.54/10.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 10.54/10.79         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 10.54/10.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 10.54/10.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.54/10.79  thf('24', plain,
% 10.54/10.79      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 10.54/10.79      inference('sup-', [status(thm)], ['22', '23'])).
% 10.54/10.79  thf('25', plain,
% 10.54/10.79      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 10.54/10.79        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.54/10.79      inference('demod', [status(thm)], ['21', '24'])).
% 10.54/10.79  thf('26', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['18', '25'])).
% 10.54/10.79  thf('27', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['5', '12'])).
% 10.54/10.79  thf('28', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['18', '25'])).
% 10.54/10.79  thf(t9_funct_1, axiom,
% 10.54/10.79    (![A:$i]:
% 10.54/10.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.54/10.79       ( ![B:$i]:
% 10.54/10.79         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.54/10.79           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 10.54/10.79               ( ![C:$i]:
% 10.54/10.79                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 10.54/10.79                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 10.54/10.79             ( ( A ) = ( B ) ) ) ) ) ))).
% 10.54/10.79  thf('29', plain,
% 10.54/10.79      (![X13 : $i, X14 : $i]:
% 10.54/10.79         (~ (v1_relat_1 @ X13)
% 10.54/10.79          | ~ (v1_funct_1 @ X13)
% 10.54/10.79          | ((X14) = (X13))
% 10.54/10.79          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ (k1_relat_1 @ X14))
% 10.54/10.79          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 10.54/10.79          | ~ (v1_funct_1 @ X14)
% 10.54/10.79          | ~ (v1_relat_1 @ X14))),
% 10.54/10.79      inference('cnf', [status(esa)], [t9_funct_1])).
% 10.54/10.79  thf('30', plain,
% 10.54/10.79      (![X0 : $i]:
% 10.54/10.79         (((sk_A) != (k1_relat_1 @ X0))
% 10.54/10.79          | ((sk_B) = (k1_xboole_0))
% 10.54/10.79          | ~ (v1_relat_1 @ sk_C_2)
% 10.54/10.79          | ~ (v1_funct_1 @ sk_C_2)
% 10.54/10.79          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.54/10.79          | ((sk_C_2) = (X0))
% 10.54/10.79          | ~ (v1_funct_1 @ X0)
% 10.54/10.79          | ~ (v1_relat_1 @ X0))),
% 10.54/10.79      inference('sup-', [status(thm)], ['28', '29'])).
% 10.54/10.79  thf('31', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf(cc1_relset_1, axiom,
% 10.54/10.79    (![A:$i,B:$i,C:$i]:
% 10.54/10.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.54/10.79       ( v1_relat_1 @ C ) ))).
% 10.54/10.79  thf('32', plain,
% 10.54/10.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.54/10.79         ((v1_relat_1 @ X15)
% 10.54/10.79          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 10.54/10.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.54/10.79  thf('33', plain, ((v1_relat_1 @ sk_C_2)),
% 10.54/10.79      inference('sup-', [status(thm)], ['31', '32'])).
% 10.54/10.79  thf('34', plain, ((v1_funct_1 @ sk_C_2)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('35', plain,
% 10.54/10.79      (![X0 : $i]:
% 10.54/10.79         (((sk_A) != (k1_relat_1 @ X0))
% 10.54/10.79          | ((sk_B) = (k1_xboole_0))
% 10.54/10.79          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.54/10.79          | ((sk_C_2) = (X0))
% 10.54/10.79          | ~ (v1_funct_1 @ X0)
% 10.54/10.79          | ~ (v1_relat_1 @ X0))),
% 10.54/10.79      inference('demod', [status(thm)], ['30', '33', '34'])).
% 10.54/10.79  thf('36', plain,
% 10.54/10.79      ((((sk_A) != (sk_A))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ~ (v1_relat_1 @ sk_D)
% 10.54/10.79        | ~ (v1_funct_1 @ sk_D)
% 10.54/10.79        | ((sk_C_2) = (sk_D))
% 10.54/10.79        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['27', '35'])).
% 10.54/10.79  thf('37', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('38', plain,
% 10.54/10.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.54/10.79         ((v1_relat_1 @ X15)
% 10.54/10.79          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 10.54/10.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.54/10.79  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 10.54/10.79      inference('sup-', [status(thm)], ['37', '38'])).
% 10.54/10.79  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('41', plain,
% 10.54/10.79      ((((sk_A) != (sk_A))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((sk_C_2) = (sk_D))
% 10.54/10.79        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0)))),
% 10.54/10.79      inference('demod', [status(thm)], ['36', '39', '40'])).
% 10.54/10.79  thf('42', plain,
% 10.54/10.79      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.54/10.79        | ((sk_C_2) = (sk_D))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0)))),
% 10.54/10.79      inference('simplify', [status(thm)], ['41'])).
% 10.54/10.79  thf('43', plain,
% 10.54/10.79      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((sk_C_2) = (sk_D)))),
% 10.54/10.79      inference('sup+', [status(thm)], ['26', '42'])).
% 10.54/10.79  thf('44', plain,
% 10.54/10.79      ((((sk_C_2) = (sk_D))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 10.54/10.79      inference('simplify', [status(thm)], ['43'])).
% 10.54/10.79  thf(t1_subset, axiom,
% 10.54/10.79    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 10.54/10.79  thf('45', plain,
% 10.54/10.79      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 10.54/10.79      inference('cnf', [status(esa)], [t1_subset])).
% 10.54/10.79  thf('46', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((sk_C_2) = (sk_D))
% 10.54/10.79        | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 10.54/10.79      inference('sup-', [status(thm)], ['44', '45'])).
% 10.54/10.79  thf('47', plain,
% 10.54/10.79      (![X33 : $i]:
% 10.54/10.79         (((k1_funct_1 @ sk_C_2 @ X33) = (k1_funct_1 @ sk_D @ X33))
% 10.54/10.79          | ~ (m1_subset_1 @ X33 @ sk_A))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('48', plain,
% 10.54/10.79      ((((sk_C_2) = (sk_D))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.54/10.79            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 10.54/10.79      inference('sup-', [status(thm)], ['46', '47'])).
% 10.54/10.79  thf('49', plain,
% 10.54/10.79      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.54/10.79          = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0)))),
% 10.54/10.79      inference('condensation', [status(thm)], ['48'])).
% 10.54/10.79  thf('50', plain,
% 10.54/10.79      (![X13 : $i, X14 : $i]:
% 10.54/10.79         (~ (v1_relat_1 @ X13)
% 10.54/10.79          | ~ (v1_funct_1 @ X13)
% 10.54/10.79          | ((X14) = (X13))
% 10.54/10.79          | ((k1_funct_1 @ X14 @ (sk_C_1 @ X13 @ X14))
% 10.54/10.79              != (k1_funct_1 @ X13 @ (sk_C_1 @ X13 @ X14)))
% 10.54/10.79          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 10.54/10.79          | ~ (v1_funct_1 @ X14)
% 10.54/10.79          | ~ (v1_relat_1 @ X14))),
% 10.54/10.79      inference('cnf', [status(esa)], [t9_funct_1])).
% 10.54/10.79  thf('51', plain,
% 10.54/10.79      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.54/10.79          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ~ (v1_relat_1 @ sk_C_2)
% 10.54/10.79        | ~ (v1_funct_1 @ sk_C_2)
% 10.54/10.79        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 10.54/10.79        | ((sk_C_2) = (sk_D))
% 10.54/10.79        | ~ (v1_funct_1 @ sk_D)
% 10.54/10.79        | ~ (v1_relat_1 @ sk_D))),
% 10.54/10.79      inference('sup-', [status(thm)], ['49', '50'])).
% 10.54/10.79  thf('52', plain, ((v1_relat_1 @ sk_C_2)),
% 10.54/10.79      inference('sup-', [status(thm)], ['31', '32'])).
% 10.54/10.79  thf('53', plain, ((v1_funct_1 @ sk_C_2)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 10.54/10.79      inference('sup-', [status(thm)], ['37', '38'])).
% 10.54/10.79  thf('56', plain,
% 10.54/10.79      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.54/10.79          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 10.54/10.79        | ((sk_C_2) = (sk_D)))),
% 10.54/10.79      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 10.54/10.79  thf('57', plain,
% 10.54/10.79      ((((sk_C_2) = (sk_D))
% 10.54/10.79        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0)))),
% 10.54/10.79      inference('simplify', [status(thm)], ['56'])).
% 10.54/10.79  thf('58', plain,
% 10.54/10.79      ((((k1_relat_1 @ sk_C_2) != (sk_A))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((sk_C_2) = (sk_D)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['13', '57'])).
% 10.54/10.79  thf('59', plain,
% 10.54/10.79      ((((sk_C_2) = (sk_D))
% 10.54/10.79        | ((sk_B) = (k1_xboole_0))
% 10.54/10.79        | ((k1_relat_1 @ sk_C_2) != (sk_A)))),
% 10.54/10.79      inference('simplify', [status(thm)], ['58'])).
% 10.54/10.79  thf('60', plain,
% 10.54/10.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['18', '25'])).
% 10.54/10.79  thf('61', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 10.54/10.79      inference('clc', [status(thm)], ['59', '60'])).
% 10.54/10.79  thf('62', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('63', plain,
% 10.54/10.79      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)
% 10.54/10.79        | ((sk_B) = (k1_xboole_0)))),
% 10.54/10.79      inference('sup-', [status(thm)], ['61', '62'])).
% 10.54/10.79  thf('64', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf(redefinition_r2_relset_1, axiom,
% 10.54/10.79    (![A:$i,B:$i,C:$i,D:$i]:
% 10.54/10.79     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.54/10.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.54/10.79       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.54/10.79  thf('65', plain,
% 10.54/10.79      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 10.54/10.79         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 10.54/10.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 10.54/10.79          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 10.54/10.79          | ((X21) != (X24)))),
% 10.54/10.79      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.54/10.79  thf('66', plain,
% 10.54/10.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.54/10.79         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 10.54/10.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 10.54/10.79      inference('simplify', [status(thm)], ['65'])).
% 10.54/10.79  thf('67', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 10.54/10.79      inference('sup-', [status(thm)], ['64', '66'])).
% 10.54/10.79  thf('68', plain, (((sk_B) = (k1_xboole_0))),
% 10.54/10.79      inference('demod', [status(thm)], ['63', '67'])).
% 10.54/10.79  thf('69', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 10.54/10.79      inference('demod', [status(thm)], ['0', '68'])).
% 10.54/10.79  thf(d3_tarski, axiom,
% 10.54/10.79    (![A:$i,B:$i]:
% 10.54/10.79     ( ( r1_tarski @ A @ B ) <=>
% 10.54/10.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 10.54/10.79  thf('70', plain,
% 10.54/10.79      (![X1 : $i, X3 : $i]:
% 10.54/10.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.54/10.79      inference('cnf', [status(esa)], [d3_tarski])).
% 10.54/10.79  thf('71', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf(t5_subset, axiom,
% 10.54/10.79    (![A:$i,B:$i,C:$i]:
% 10.54/10.79     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 10.54/10.79          ( v1_xboole_0 @ C ) ) ))).
% 10.54/10.79  thf('72', plain,
% 10.54/10.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.54/10.79         (~ (r2_hidden @ X10 @ X11)
% 10.54/10.79          | ~ (v1_xboole_0 @ X12)
% 10.54/10.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 10.54/10.79      inference('cnf', [status(esa)], [t5_subset])).
% 10.54/10.79  thf('73', plain,
% 10.54/10.79      (![X0 : $i]:
% 10.54/10.79         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.54/10.79          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 10.54/10.79      inference('sup-', [status(thm)], ['71', '72'])).
% 10.54/10.79  thf('74', plain, (((sk_B) = (k1_xboole_0))),
% 10.54/10.79      inference('demod', [status(thm)], ['63', '67'])).
% 10.54/10.79  thf(t113_zfmisc_1, axiom,
% 10.54/10.79    (![A:$i,B:$i]:
% 10.54/10.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 10.54/10.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 10.54/10.79  thf('75', plain,
% 10.54/10.79      (![X6 : $i, X7 : $i]:
% 10.54/10.79         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 10.54/10.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.54/10.79  thf('76', plain,
% 10.54/10.79      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 10.54/10.79      inference('simplify', [status(thm)], ['75'])).
% 10.54/10.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 10.54/10.79  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.54/10.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.54/10.79  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_2)),
% 10.54/10.79      inference('demod', [status(thm)], ['73', '74', '76', '77'])).
% 10.54/10.79  thf('79', plain, (![X0 : $i]: (r1_tarski @ sk_C_2 @ X0)),
% 10.54/10.79      inference('sup-', [status(thm)], ['70', '78'])).
% 10.54/10.79  thf(t3_xboole_1, axiom,
% 10.54/10.79    (![A:$i]:
% 10.54/10.79     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.54/10.79  thf('80', plain,
% 10.54/10.79      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 10.54/10.79      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.54/10.79  thf('81', plain, (((sk_C_2) = (k1_xboole_0))),
% 10.54/10.79      inference('sup-', [status(thm)], ['79', '80'])).
% 10.54/10.79  thf('82', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D)),
% 10.54/10.79      inference('demod', [status(thm)], ['69', '81'])).
% 10.54/10.79  thf('83', plain,
% 10.54/10.79      (![X1 : $i, X3 : $i]:
% 10.54/10.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.54/10.79      inference('cnf', [status(esa)], [d3_tarski])).
% 10.54/10.79  thf('84', plain,
% 10.54/10.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.54/10.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.79  thf('85', plain,
% 10.54/10.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.54/10.79         (~ (r2_hidden @ X10 @ X11)
% 10.54/10.79          | ~ (v1_xboole_0 @ X12)
% 10.54/10.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 10.54/10.79      inference('cnf', [status(esa)], [t5_subset])).
% 10.54/10.79  thf('86', plain,
% 10.54/10.79      (![X0 : $i]:
% 10.54/10.79         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 10.54/10.79          | ~ (r2_hidden @ X0 @ sk_D))),
% 10.54/10.79      inference('sup-', [status(thm)], ['84', '85'])).
% 10.54/10.79  thf('87', plain, (((sk_B) = (k1_xboole_0))),
% 10.54/10.79      inference('demod', [status(thm)], ['63', '67'])).
% 10.54/10.79  thf('88', plain,
% 10.54/10.79      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 10.54/10.79      inference('simplify', [status(thm)], ['75'])).
% 10.54/10.79  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.54/10.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.54/10.79  thf('90', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)),
% 10.54/10.79      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 10.54/10.79  thf('91', plain, (![X0 : $i]: (r1_tarski @ sk_D @ X0)),
% 10.54/10.79      inference('sup-', [status(thm)], ['83', '90'])).
% 10.54/10.79  thf('92', plain,
% 10.54/10.79      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 10.54/10.79      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.54/10.79  thf('93', plain, (((sk_D) = (k1_xboole_0))),
% 10.54/10.79      inference('sup-', [status(thm)], ['91', '92'])).
% 10.54/10.79  thf('94', plain,
% 10.54/10.79      (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 10.54/10.79      inference('demod', [status(thm)], ['82', '93'])).
% 10.54/10.79  thf('95', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 10.54/10.79      inference('sup-', [status(thm)], ['64', '66'])).
% 10.54/10.79  thf('96', plain, (((sk_B) = (k1_xboole_0))),
% 10.54/10.79      inference('demod', [status(thm)], ['63', '67'])).
% 10.54/10.79  thf('97', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 10.54/10.79      inference('demod', [status(thm)], ['95', '96'])).
% 10.54/10.79  thf('98', plain, (((sk_C_2) = (k1_xboole_0))),
% 10.54/10.79      inference('sup-', [status(thm)], ['79', '80'])).
% 10.54/10.79  thf('99', plain, (((sk_C_2) = (k1_xboole_0))),
% 10.54/10.79      inference('sup-', [status(thm)], ['79', '80'])).
% 10.54/10.79  thf('100', plain,
% 10.54/10.79      ((r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 10.54/10.79      inference('demod', [status(thm)], ['97', '98', '99'])).
% 10.54/10.79  thf('101', plain, ($false), inference('demod', [status(thm)], ['94', '100'])).
% 10.54/10.79  
% 10.54/10.79  % SZS output end Refutation
% 10.54/10.79  
% 10.54/10.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
