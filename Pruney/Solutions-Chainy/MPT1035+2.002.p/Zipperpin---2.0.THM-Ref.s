%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iszyxCcQv

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:12 EST 2020

% Result     : Theorem 11.79s
% Output     : Refutation 11.79s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 851 expanded)
%              Number of leaves         :   37 ( 256 expanded)
%              Depth                    :   22
%              Number of atoms          : 2442 (14962 expanded)
%              Number of equality atoms :  211 (1139 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t145_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( A = k1_xboole_0 ) )
           => ( ( r1_partfun1 @ C @ D )
            <=> ! [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( A = k1_xboole_0 ) )
             => ( ( r1_partfun1 @ C @ D )
              <=> ! [E: $i] :
                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                   => ( ( k1_funct_1 @ C @ E )
                      = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_funct_2])).

thf('0',plain,(
    ! [X31: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ X31 )
        = ( k1_funct_1 @ sk_D @ X31 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2 )
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_E @ k1_xboole_0 )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_E @ X0 )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r1_partfun1 @ X29 @ X28 )
      | ( ( k1_funct_1 @ X29 @ X30 )
        = ( k1_funct_1 @ X28 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('36',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ~ ( v1_funct_1 @ sk_C_2 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X1 )
          = ( k1_funct_1 @ X0 @ X1 ) )
        | ~ ( r1_partfun1 @ sk_C_2 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_2 @ X1 )
          = ( k1_funct_1 @ X0 @ X1 ) )
        | ~ ( r1_partfun1 @ sk_C_2 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','40','41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r1_partfun1 @ sk_C_2 @ X0 )
        | ( ( k1_funct_1 @ sk_C_2 @ sk_E )
          = ( k1_funct_1 @ X0 @ sk_E ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['24','43'])).

thf('45',plain,
    ( ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
        = ( k1_funct_1 @ sk_D @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['1','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['51'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('59',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('61',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['66'])).

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

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('89',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ k1_xboole_0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','90'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('94',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('96',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( r2_hidden @ ( sk_C_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X29 ) )
      | ( r1_partfun1 @ X29 @ X28 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('105',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('107',plain,
    ( ! [X31: $i] :
        ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X31 )
          = ( k1_funct_1 @ sk_D @ X31 ) ) )
   <= ! [X31: $i] :
        ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X31 )
          = ( k1_funct_1 @ sk_D @ X31 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X31: $i] :
        ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X31 )
          = ( k1_funct_1 @ sk_D @ X31 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k1_funct_1 @ X29 @ ( sk_C_1 @ X28 @ X29 ) )
       != ( k1_funct_1 @ X28 @ ( sk_C_1 @ X28 @ X29 ) ) )
      | ( r1_partfun1 @ X29 @ X28 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('111',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('113',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('115',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['66'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('118',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','117'])).

thf('119',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['51'])).

thf('121',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) )
    | ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('123',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('124',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('127',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('132',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','132'])).

thf('134',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('135',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('136',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','138'])).

thf('140',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','139'])).

thf('141',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( r2_hidden @ ( sk_C_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X29 ) )
      | ( r1_partfun1 @ X29 @ X28 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','145'])).

thf('147',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('148',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('149',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('151',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( r1_partfun1 @ sk_C_2 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X31: $i] :
        ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X31 )
          = ( k1_funct_1 @ sk_D @ X31 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k1_funct_1 @ X29 @ ( sk_C_1 @ X28 @ X29 ) )
       != ( k1_funct_1 @ X28 @ ( sk_C_1 @ X28 @ X29 ) ) )
      | ( r1_partfun1 @ X29 @ X28 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('159',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('161',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('163',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','139'])).

thf('164',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('165',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('167',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164','165','166'])).

thf('168',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['51'])).

thf('170',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ! [X31: $i] :
          ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X31 )
            = ( k1_funct_1 @ sk_D @ X31 ) ) )
    | ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ! [X31: $i] :
        ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X31 )
          = ( k1_funct_1 @ sk_D @ X31 ) ) )
    | ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('172',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['5'])).

thf('173',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('174',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('175',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['66'])).

thf('176',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('177',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('178',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('180',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r1_partfun1 @ X29 @ X28 )
      | ( ( k1_funct_1 @ X29 @ X30 )
        = ( k1_funct_1 @ X28 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['174','189'])).

thf('191',plain,
    ( ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
        = ( k1_funct_1 @ sk_D @ sk_E ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['173','190'])).

thf('192',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['51'])).

thf('193',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('196',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( sk_B != k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('199',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['54','55','121','170','171','172','197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iszyxCcQv
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % DateTime   : Tue Dec  1 19:28:22 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running portfolio for 600 s
% 0.18/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.34  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 11.79/11.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.79/11.98  % Solved by: fo/fo7.sh
% 11.79/11.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.79/11.98  % done 4509 iterations in 11.558s
% 11.79/11.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.79/11.98  % SZS output start Refutation
% 11.79/11.98  thf(sk_E_type, type, sk_E: $i).
% 11.79/11.98  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 11.79/11.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.79/11.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.79/11.98  thf(sk_A_type, type, sk_A: $i).
% 11.79/11.98  thf(sk_D_type, type, sk_D: $i).
% 11.79/11.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 11.79/11.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 11.79/11.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 11.79/11.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.79/11.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.79/11.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.79/11.98  thf(sk_C_2_type, type, sk_C_2: $i).
% 11.79/11.98  thf(sk_B_type, type, sk_B: $i).
% 11.79/11.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.79/11.98  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 11.79/11.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.79/11.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.79/11.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.79/11.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.79/11.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.79/11.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 11.79/11.98  thf(t145_funct_2, conjecture,
% 11.79/11.98    (![A:$i,B:$i,C:$i]:
% 11.79/11.98     ( ( ( v1_funct_1 @ C ) & 
% 11.79/11.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.79/11.98       ( ![D:$i]:
% 11.79/11.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.79/11.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.79/11.98           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.79/11.98             ( ( r1_partfun1 @ C @ D ) <=>
% 11.79/11.98               ( ![E:$i]:
% 11.79/11.98                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 11.79/11.98                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 11.79/11.98  thf(zf_stmt_0, negated_conjecture,
% 11.79/11.98    (~( ![A:$i,B:$i,C:$i]:
% 11.79/11.98        ( ( ( v1_funct_1 @ C ) & 
% 11.79/11.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.79/11.98          ( ![D:$i]:
% 11.79/11.98            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.79/11.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.79/11.98              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.79/11.98                ( ( r1_partfun1 @ C @ D ) <=>
% 11.79/11.98                  ( ![E:$i]:
% 11.79/11.98                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 11.79/11.98                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 11.79/11.98    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 11.79/11.98  thf('0', plain,
% 11.79/11.98      (![X31 : $i]:
% 11.79/11.98         (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98          | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31))
% 11.79/11.98          | (r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('1', plain,
% 11.79/11.98      (((r1_partfun1 @ sk_C_2 @ sk_D)) <= (((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 11.79/11.98      inference('split', [status(esa)], ['0'])).
% 11.79/11.98  thf('2', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf(redefinition_k1_relset_1, axiom,
% 11.79/11.98    (![A:$i,B:$i,C:$i]:
% 11.79/11.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.79/11.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 11.79/11.98  thf('3', plain,
% 11.79/11.98      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.79/11.98         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 11.79/11.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 11.79/11.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.79/11.98  thf('4', plain,
% 11.79/11.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 11.79/11.98      inference('sup-', [status(thm)], ['2', '3'])).
% 11.79/11.98  thf('5', plain,
% 11.79/11.98      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98        | ~ (r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('6', plain,
% 11.79/11.98      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 11.79/11.98         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('split', [status(esa)], ['5'])).
% 11.79/11.98  thf('7', plain,
% 11.79/11.98      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_2)))
% 11.79/11.98         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['4', '6'])).
% 11.79/11.98  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('9', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('split', [status(esa)], ['8'])).
% 11.79/11.98  thf('10', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('11', plain,
% 11.79/11.98      (((m1_subset_1 @ sk_C_2 @ 
% 11.79/11.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['9', '10'])).
% 11.79/11.98  thf(dt_k1_relset_1, axiom,
% 11.79/11.98    (![A:$i,B:$i,C:$i]:
% 11.79/11.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.79/11.98       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 11.79/11.98  thf('12', plain,
% 11.79/11.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.79/11.98         ((m1_subset_1 @ (k1_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 11.79/11.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 11.79/11.98      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 11.79/11.98  thf('13', plain,
% 11.79/11.98      (((m1_subset_1 @ (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2) @ 
% 11.79/11.98         (k1_zfmisc_1 @ k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['11', '12'])).
% 11.79/11.98  thf('14', plain,
% 11.79/11.98      (((m1_subset_1 @ sk_C_2 @ 
% 11.79/11.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['9', '10'])).
% 11.79/11.98  thf('15', plain,
% 11.79/11.98      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.79/11.98         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 11.79/11.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 11.79/11.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.79/11.98  thf('16', plain,
% 11.79/11.98      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['14', '15'])).
% 11.79/11.98  thf('17', plain,
% 11.79/11.98      (((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['13', '16'])).
% 11.79/11.98  thf(l3_subset_1, axiom,
% 11.79/11.98    (![A:$i,B:$i]:
% 11.79/11.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.79/11.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 11.79/11.98  thf('18', plain,
% 11.79/11.98      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.79/11.98         (~ (r2_hidden @ X8 @ X9)
% 11.79/11.98          | (r2_hidden @ X8 @ X10)
% 11.79/11.98          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 11.79/11.98      inference('cnf', [status(esa)], [l3_subset_1])).
% 11.79/11.98  thf('19', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          ((r2_hidden @ X0 @ k1_xboole_0)
% 11.79/11.98           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['17', '18'])).
% 11.79/11.98  thf('20', plain,
% 11.79/11.98      (((r2_hidden @ sk_E @ k1_xboole_0))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['7', '19'])).
% 11.79/11.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 11.79/11.98  thf('21', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 11.79/11.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.79/11.98  thf(d3_tarski, axiom,
% 11.79/11.98    (![A:$i,B:$i]:
% 11.79/11.98     ( ( r1_tarski @ A @ B ) <=>
% 11.79/11.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 11.79/11.98  thf('22', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.79/11.98         (~ (r2_hidden @ X0 @ X1)
% 11.79/11.98          | (r2_hidden @ X0 @ X2)
% 11.79/11.98          | ~ (r1_tarski @ X1 @ X2))),
% 11.79/11.98      inference('cnf', [status(esa)], [d3_tarski])).
% 11.79/11.98  thf('23', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i]:
% 11.79/11.98         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 11.79/11.98      inference('sup-', [status(thm)], ['21', '22'])).
% 11.79/11.98  thf('24', plain,
% 11.79/11.98      ((![X0 : $i]: (r2_hidden @ sk_E @ X0))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['20', '23'])).
% 11.79/11.98  thf('25', plain,
% 11.79/11.98      (![X1 : $i, X3 : $i]:
% 11.79/11.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.79/11.98      inference('cnf', [status(esa)], [d3_tarski])).
% 11.79/11.98  thf('26', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          ((r2_hidden @ X0 @ k1_xboole_0)
% 11.79/11.98           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['17', '18'])).
% 11.79/11.98  thf('27', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0)
% 11.79/11.98           | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_2)) @ k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['25', '26'])).
% 11.79/11.98  thf('28', plain,
% 11.79/11.98      (![X1 : $i, X3 : $i]:
% 11.79/11.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.79/11.98      inference('cnf', [status(esa)], [d3_tarski])).
% 11.79/11.98  thf('29', plain,
% 11.79/11.98      ((((r1_tarski @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0)
% 11.79/11.98         | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['27', '28'])).
% 11.79/11.98  thf('30', plain,
% 11.79/11.98      (((r1_tarski @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('simplify', [status(thm)], ['29'])).
% 11.79/11.98  thf('31', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 11.79/11.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.79/11.98  thf(d10_xboole_0, axiom,
% 11.79/11.98    (![A:$i,B:$i]:
% 11.79/11.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.79/11.98  thf('32', plain,
% 11.79/11.98      (![X4 : $i, X6 : $i]:
% 11.79/11.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 11.79/11.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.79/11.98  thf('33', plain,
% 11.79/11.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['31', '32'])).
% 11.79/11.98  thf('34', plain,
% 11.79/11.98      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['30', '33'])).
% 11.79/11.98  thf(t132_partfun1, axiom,
% 11.79/11.98    (![A:$i]:
% 11.79/11.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.79/11.98       ( ![B:$i]:
% 11.79/11.98         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 11.79/11.98           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 11.79/11.98             ( ( r1_partfun1 @ A @ B ) <=>
% 11.79/11.98               ( ![C:$i]:
% 11.79/11.98                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 11.79/11.98                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 11.79/11.98  thf('35', plain,
% 11.79/11.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 11.79/11.98         (~ (v1_relat_1 @ X28)
% 11.79/11.98          | ~ (v1_funct_1 @ X28)
% 11.79/11.98          | ~ (r1_partfun1 @ X29 @ X28)
% 11.79/11.98          | ((k1_funct_1 @ X29 @ X30) = (k1_funct_1 @ X28 @ X30))
% 11.79/11.98          | ~ (r2_hidden @ X30 @ (k1_relat_1 @ X29))
% 11.79/11.98          | ~ (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 11.79/11.98          | ~ (v1_funct_1 @ X29)
% 11.79/11.98          | ~ (v1_relat_1 @ X29))),
% 11.79/11.98      inference('cnf', [status(esa)], [t132_partfun1])).
% 11.79/11.98  thf('36', plain,
% 11.79/11.98      ((![X0 : $i, X1 : $i]:
% 11.79/11.98          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 11.79/11.98           | ~ (v1_relat_1 @ sk_C_2)
% 11.79/11.98           | ~ (v1_funct_1 @ sk_C_2)
% 11.79/11.98           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X1) = (k1_funct_1 @ X0 @ X1))
% 11.79/11.98           | ~ (r1_partfun1 @ sk_C_2 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | ~ (v1_relat_1 @ X0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['34', '35'])).
% 11.79/11.98  thf('37', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 11.79/11.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.79/11.98  thf('38', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf(cc1_relset_1, axiom,
% 11.79/11.98    (![A:$i,B:$i,C:$i]:
% 11.79/11.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.79/11.98       ( v1_relat_1 @ C ) ))).
% 11.79/11.98  thf('39', plain,
% 11.79/11.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 11.79/11.98         ((v1_relat_1 @ X11)
% 11.79/11.98          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 11.79/11.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.79/11.98  thf('40', plain, ((v1_relat_1 @ sk_C_2)),
% 11.79/11.98      inference('sup-', [status(thm)], ['38', '39'])).
% 11.79/11.98  thf('41', plain, ((v1_funct_1 @ sk_C_2)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('42', plain,
% 11.79/11.98      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['30', '33'])).
% 11.79/11.98  thf('43', plain,
% 11.79/11.98      ((![X0 : $i, X1 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X1 @ k1_xboole_0)
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X1) = (k1_funct_1 @ X0 @ X1))
% 11.79/11.98           | ~ (r1_partfun1 @ sk_C_2 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | ~ (v1_relat_1 @ X0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['36', '37', '40', '41', '42'])).
% 11.79/11.98  thf('44', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (v1_relat_1 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | ~ (r1_partfun1 @ sk_C_2 @ X0)
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ X0 @ sk_E))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['24', '43'])).
% 11.79/11.98  thf('45', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))
% 11.79/11.98         | ~ (v1_funct_1 @ sk_D)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_D)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['1', '44'])).
% 11.79/11.98  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('47', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('48', plain,
% 11.79/11.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 11.79/11.98         ((v1_relat_1 @ X11)
% 11.79/11.98          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 11.79/11.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.79/11.98  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 11.79/11.98      inference('sup-', [status(thm)], ['47', '48'])).
% 11.79/11.98  thf('50', plain,
% 11.79/11.98      ((((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('demod', [status(thm)], ['45', '46', '49'])).
% 11.79/11.98  thf('51', plain,
% 11.79/11.98      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 11.79/11.98        | ~ (r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('52', plain,
% 11.79/11.98      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 11.79/11.98         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 11.79/11.98      inference('split', [status(esa)], ['51'])).
% 11.79/11.98  thf('53', plain,
% 11.79/11.98      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 11.79/11.98         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 11.79/11.98             (((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['50', '52'])).
% 11.79/11.98  thf('54', plain,
% 11.79/11.98      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_partfun1 @ sk_C_2 @ sk_D)) | 
% 11.79/11.98       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 11.79/11.98       (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 11.79/11.98      inference('simplify', [status(thm)], ['53'])).
% 11.79/11.98  thf('55', plain,
% 11.79/11.98      (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 11.79/11.98       ~ ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('split', [status(esa)], ['51'])).
% 11.79/11.98  thf('56', plain,
% 11.79/11.98      (![X1 : $i, X3 : $i]:
% 11.79/11.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.79/11.98      inference('cnf', [status(esa)], [d3_tarski])).
% 11.79/11.98  thf('57', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('58', plain,
% 11.79/11.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.79/11.98         ((m1_subset_1 @ (k1_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 11.79/11.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 11.79/11.98      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 11.79/11.98  thf('59', plain,
% 11.79/11.98      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 11.79/11.98        (k1_zfmisc_1 @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['57', '58'])).
% 11.79/11.98  thf('60', plain,
% 11.79/11.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 11.79/11.98      inference('sup-', [status(thm)], ['2', '3'])).
% 11.79/11.98  thf('61', plain,
% 11.79/11.98      ((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 11.79/11.98      inference('demod', [status(thm)], ['59', '60'])).
% 11.79/11.98  thf('62', plain,
% 11.79/11.98      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.79/11.98         (~ (r2_hidden @ X8 @ X9)
% 11.79/11.98          | (r2_hidden @ X8 @ X10)
% 11.79/11.98          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 11.79/11.98      inference('cnf', [status(esa)], [l3_subset_1])).
% 11.79/11.98  thf('63', plain,
% 11.79/11.98      (![X0 : $i]:
% 11.79/11.98         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['61', '62'])).
% 11.79/11.98  thf('64', plain,
% 11.79/11.98      (![X0 : $i]:
% 11.79/11.98         ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0)
% 11.79/11.98          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_2)) @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['56', '63'])).
% 11.79/11.98  thf('65', plain,
% 11.79/11.98      (![X1 : $i, X3 : $i]:
% 11.79/11.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.79/11.98      inference('cnf', [status(esa)], [d3_tarski])).
% 11.79/11.98  thf('66', plain,
% 11.79/11.98      (((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)
% 11.79/11.98        | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['64', '65'])).
% 11.79/11.98  thf('67', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 11.79/11.98      inference('simplify', [status(thm)], ['66'])).
% 11.79/11.98  thf(d1_funct_2, axiom,
% 11.79/11.98    (![A:$i,B:$i,C:$i]:
% 11.79/11.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.79/11.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 11.79/11.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 11.79/11.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 11.79/11.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.79/11.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 11.79/11.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 11.79/11.98  thf(zf_stmt_1, axiom,
% 11.79/11.98    (![B:$i,A:$i]:
% 11.79/11.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 11.79/11.98       ( zip_tseitin_0 @ B @ A ) ))).
% 11.79/11.98  thf('68', plain,
% 11.79/11.98      (![X20 : $i, X21 : $i]:
% 11.79/11.98         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.79/11.98  thf('69', plain,
% 11.79/11.98      (![X20 : $i, X21 : $i]:
% 11.79/11.98         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.79/11.98  thf('70', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 11.79/11.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.79/11.98  thf('71', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.79/11.98         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 11.79/11.98      inference('sup+', [status(thm)], ['69', '70'])).
% 11.79/11.98  thf('72', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 11.79/11.98  thf(zf_stmt_3, axiom,
% 11.79/11.98    (![C:$i,B:$i,A:$i]:
% 11.79/11.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 11.79/11.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 11.79/11.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 11.79/11.98  thf(zf_stmt_5, axiom,
% 11.79/11.98    (![A:$i,B:$i,C:$i]:
% 11.79/11.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.79/11.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 11.79/11.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 11.79/11.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 11.79/11.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 11.79/11.98  thf('73', plain,
% 11.79/11.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.79/11.98         (~ (zip_tseitin_0 @ X25 @ X26)
% 11.79/11.98          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 11.79/11.98          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.79/11.98  thf('74', plain,
% 11.79/11.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['72', '73'])).
% 11.79/11.98  thf('75', plain,
% 11.79/11.98      (![X0 : $i]:
% 11.79/11.98         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['71', '74'])).
% 11.79/11.98  thf('76', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('77', plain,
% 11.79/11.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.79/11.98         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 11.79/11.98          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 11.79/11.98          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.79/11.98  thf('78', plain,
% 11.79/11.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 11.79/11.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['76', '77'])).
% 11.79/11.98  thf('79', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('80', plain,
% 11.79/11.98      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.79/11.98         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 11.79/11.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 11.79/11.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.79/11.98  thf('81', plain,
% 11.79/11.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 11.79/11.98      inference('sup-', [status(thm)], ['79', '80'])).
% 11.79/11.98  thf('82', plain,
% 11.79/11.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.79/11.98      inference('demod', [status(thm)], ['78', '81'])).
% 11.79/11.98  thf('83', plain,
% 11.79/11.98      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['75', '82'])).
% 11.79/11.98  thf('84', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.79/11.98         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 11.79/11.98      inference('sup+', [status(thm)], ['69', '70'])).
% 11.79/11.98  thf('85', plain,
% 11.79/11.98      (![X4 : $i, X6 : $i]:
% 11.79/11.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 11.79/11.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.79/11.98  thf('86', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.79/11.98         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['84', '85'])).
% 11.79/11.98  thf('87', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i]:
% 11.79/11.98         (((sk_A) = (k1_relat_1 @ sk_D))
% 11.79/11.98          | ((sk_B) = (X0))
% 11.79/11.98          | (zip_tseitin_0 @ X0 @ X1))),
% 11.79/11.98      inference('sup-', [status(thm)], ['83', '86'])).
% 11.79/11.98  thf('88', plain,
% 11.79/11.98      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('split', [status(esa)], ['8'])).
% 11.79/11.98  thf('89', plain,
% 11.79/11.98      ((![X0 : $i, X1 : $i]:
% 11.79/11.98          (((X0) != (k1_xboole_0))
% 11.79/11.98           | (zip_tseitin_0 @ X0 @ X1)
% 11.79/11.98           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['87', '88'])).
% 11.79/11.98  thf('90', plain,
% 11.79/11.98      ((![X1 : $i]:
% 11.79/11.98          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ k1_xboole_0 @ X1)))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('simplify', [status(thm)], ['89'])).
% 11.79/11.98  thf('91', plain,
% 11.79/11.98      ((![X0 : $i, X1 : $i, X2 : $i]:
% 11.79/11.98          ((zip_tseitin_0 @ X0 @ X1)
% 11.79/11.98           | (zip_tseitin_0 @ X0 @ X2)
% 11.79/11.98           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['68', '90'])).
% 11.79/11.98  thf('92', plain,
% 11.79/11.98      ((![X0 : $i, X1 : $i]:
% 11.79/11.98          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('condensation', [status(thm)], ['91'])).
% 11.79/11.98  thf('93', plain,
% 11.79/11.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['72', '73'])).
% 11.79/11.98  thf('94', plain,
% 11.79/11.98      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['92', '93'])).
% 11.79/11.98  thf('95', plain,
% 11.79/11.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.79/11.98      inference('demod', [status(thm)], ['78', '81'])).
% 11.79/11.98  thf('96', plain,
% 11.79/11.98      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('clc', [status(thm)], ['94', '95'])).
% 11.79/11.98  thf('97', plain,
% 11.79/11.98      (![X28 : $i, X29 : $i]:
% 11.79/11.98         (~ (v1_relat_1 @ X28)
% 11.79/11.98          | ~ (v1_funct_1 @ X28)
% 11.79/11.98          | (r2_hidden @ (sk_C_1 @ X28 @ X29) @ (k1_relat_1 @ X29))
% 11.79/11.98          | (r1_partfun1 @ X29 @ X28)
% 11.79/11.98          | ~ (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 11.79/11.98          | ~ (v1_funct_1 @ X29)
% 11.79/11.98          | ~ (v1_relat_1 @ X29))),
% 11.79/11.98      inference('cnf', [status(esa)], [t132_partfun1])).
% 11.79/11.98  thf('98', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 11.79/11.98           | ~ (v1_relat_1 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | (r1_partfun1 @ X0 @ sk_D)
% 11.79/11.98           | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 11.79/11.98           | ~ (v1_funct_1 @ sk_D)
% 11.79/11.98           | ~ (v1_relat_1 @ sk_D)))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['96', '97'])).
% 11.79/11.98  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 11.79/11.98      inference('sup-', [status(thm)], ['47', '48'])).
% 11.79/11.98  thf('101', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 11.79/11.98           | ~ (v1_relat_1 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | (r1_partfun1 @ X0 @ sk_D)
% 11.79/11.98           | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['98', '99', '100'])).
% 11.79/11.98  thf('102', plain,
% 11.79/11.98      ((((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ~ (v1_funct_1 @ sk_C_2)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_C_2))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['67', '101'])).
% 11.79/11.98  thf('103', plain, ((v1_funct_1 @ sk_C_2)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('104', plain, ((v1_relat_1 @ sk_C_2)),
% 11.79/11.98      inference('sup-', [status(thm)], ['38', '39'])).
% 11.79/11.98  thf('105', plain,
% 11.79/11.98      ((((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['102', '103', '104'])).
% 11.79/11.98  thf('106', plain,
% 11.79/11.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 11.79/11.98      inference('sup-', [status(thm)], ['2', '3'])).
% 11.79/11.98  thf('107', plain,
% 11.79/11.98      ((![X31 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31))))
% 11.79/11.98         <= ((![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('split', [status(esa)], ['0'])).
% 11.79/11.98  thf('108', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 11.79/11.98         <= ((![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['106', '107'])).
% 11.79/11.98  thf('109', plain,
% 11.79/11.98      ((((r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 11.79/11.98             = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['105', '108'])).
% 11.79/11.98  thf('110', plain,
% 11.79/11.98      (![X28 : $i, X29 : $i]:
% 11.79/11.98         (~ (v1_relat_1 @ X28)
% 11.79/11.98          | ~ (v1_funct_1 @ X28)
% 11.79/11.98          | ((k1_funct_1 @ X29 @ (sk_C_1 @ X28 @ X29))
% 11.79/11.98              != (k1_funct_1 @ X28 @ (sk_C_1 @ X28 @ X29)))
% 11.79/11.98          | (r1_partfun1 @ X29 @ X28)
% 11.79/11.98          | ~ (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 11.79/11.98          | ~ (v1_funct_1 @ X29)
% 11.79/11.98          | ~ (v1_relat_1 @ X29))),
% 11.79/11.98      inference('cnf', [status(esa)], [t132_partfun1])).
% 11.79/11.98  thf('111', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 11.79/11.98           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_C_2)
% 11.79/11.98         | ~ (v1_funct_1 @ sk_C_2)
% 11.79/11.98         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_2) @ (k1_relat_1 @ sk_D))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ~ (v1_funct_1 @ sk_D)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_D)))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['109', '110'])).
% 11.79/11.98  thf('112', plain, ((v1_relat_1 @ sk_C_2)),
% 11.79/11.98      inference('sup-', [status(thm)], ['38', '39'])).
% 11.79/11.98  thf('113', plain, ((v1_funct_1 @ sk_C_2)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('114', plain,
% 11.79/11.98      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('clc', [status(thm)], ['94', '95'])).
% 11.79/11.98  thf('115', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 11.79/11.98      inference('simplify', [status(thm)], ['66'])).
% 11.79/11.98  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 11.79/11.98      inference('sup-', [status(thm)], ['47', '48'])).
% 11.79/11.98  thf('118', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 11.79/11.98           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('demod', [status(thm)],
% 11.79/11.98                ['111', '112', '113', '114', '115', '116', '117'])).
% 11.79/11.98  thf('119', plain,
% 11.79/11.98      (((r1_partfun1 @ sk_C_2 @ sk_D))
% 11.79/11.98         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('simplify', [status(thm)], ['118'])).
% 11.79/11.98  thf('120', plain,
% 11.79/11.98      ((~ (r1_partfun1 @ sk_C_2 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 11.79/11.98      inference('split', [status(esa)], ['51'])).
% 11.79/11.98  thf('121', plain,
% 11.79/11.98      ((((sk_B) = (k1_xboole_0))) | 
% 11.79/11.98       ~
% 11.79/11.98       (![X31 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))) | 
% 11.79/11.98       ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('sup-', [status(thm)], ['119', '120'])).
% 11.79/11.98  thf('122', plain,
% 11.79/11.98      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['30', '33'])).
% 11.79/11.98  thf('123', plain,
% 11.79/11.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('split', [status(esa)], ['8'])).
% 11.79/11.98  thf('124', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('125', plain,
% 11.79/11.98      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['123', '124'])).
% 11.79/11.98  thf('126', plain,
% 11.79/11.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.79/11.98         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 11.79/11.98          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 11.79/11.98          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.79/11.98  thf('127', plain,
% 11.79/11.98      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 11.79/11.98         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['125', '126'])).
% 11.79/11.98  thf('128', plain,
% 11.79/11.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('split', [status(esa)], ['8'])).
% 11.79/11.98  thf('129', plain,
% 11.79/11.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('130', plain,
% 11.79/11.98      (((m1_subset_1 @ sk_D @ 
% 11.79/11.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['128', '129'])).
% 11.79/11.98  thf('131', plain,
% 11.79/11.98      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.79/11.98         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 11.79/11.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 11.79/11.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.79/11.98  thf('132', plain,
% 11.79/11.98      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['130', '131'])).
% 11.79/11.98  thf('133', plain,
% 11.79/11.98      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 11.79/11.98         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['127', '132'])).
% 11.79/11.98  thf('134', plain,
% 11.79/11.98      (((m1_subset_1 @ sk_D @ 
% 11.79/11.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['128', '129'])).
% 11.79/11.98  thf('135', plain,
% 11.79/11.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.79/11.98         (~ (zip_tseitin_0 @ X25 @ X26)
% 11.79/11.98          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 11.79/11.98          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 11.79/11.98  thf('136', plain,
% 11.79/11.98      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 11.79/11.98         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['134', '135'])).
% 11.79/11.98  thf('137', plain,
% 11.79/11.98      (![X20 : $i, X21 : $i]:
% 11.79/11.98         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.79/11.98  thf('138', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 11.79/11.98      inference('simplify', [status(thm)], ['137'])).
% 11.79/11.98  thf('139', plain,
% 11.79/11.98      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['136', '138'])).
% 11.79/11.98  thf('140', plain,
% 11.79/11.98      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['133', '139'])).
% 11.79/11.98  thf('141', plain,
% 11.79/11.98      (![X28 : $i, X29 : $i]:
% 11.79/11.98         (~ (v1_relat_1 @ X28)
% 11.79/11.98          | ~ (v1_funct_1 @ X28)
% 11.79/11.98          | (r2_hidden @ (sk_C_1 @ X28 @ X29) @ (k1_relat_1 @ X29))
% 11.79/11.98          | (r1_partfun1 @ X29 @ X28)
% 11.79/11.98          | ~ (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 11.79/11.98          | ~ (v1_funct_1 @ X29)
% 11.79/11.98          | ~ (v1_relat_1 @ X29))),
% 11.79/11.98      inference('cnf', [status(esa)], [t132_partfun1])).
% 11.79/11.98  thf('142', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 11.79/11.98           | ~ (v1_relat_1 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | (r1_partfun1 @ X0 @ sk_D)
% 11.79/11.98           | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 11.79/11.98           | ~ (v1_funct_1 @ sk_D)
% 11.79/11.98           | ~ (v1_relat_1 @ sk_D)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['140', '141'])).
% 11.79/11.98  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 11.79/11.98      inference('sup-', [status(thm)], ['47', '48'])).
% 11.79/11.98  thf('145', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 11.79/11.98           | ~ (v1_relat_1 @ X0)
% 11.79/11.98           | ~ (v1_funct_1 @ X0)
% 11.79/11.98           | (r1_partfun1 @ X0 @ sk_D)
% 11.79/11.98           | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['142', '143', '144'])).
% 11.79/11.98  thf('146', plain,
% 11.79/11.98      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 11.79/11.98         | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ~ (v1_funct_1 @ sk_C_2)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_C_2))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['122', '145'])).
% 11.79/11.98  thf('147', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 11.79/11.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.79/11.98  thf('148', plain,
% 11.79/11.98      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['30', '33'])).
% 11.79/11.98  thf('149', plain, ((v1_funct_1 @ sk_C_2)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('150', plain, ((v1_relat_1 @ sk_C_2)),
% 11.79/11.98      inference('sup-', [status(thm)], ['38', '39'])).
% 11.79/11.98  thf('151', plain,
% 11.79/11.98      ((((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ k1_xboole_0)
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 11.79/11.98  thf('152', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i]:
% 11.79/11.98         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 11.79/11.98      inference('sup-', [status(thm)], ['21', '22'])).
% 11.79/11.98  thf('153', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          ((r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98           | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ X0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['151', '152'])).
% 11.79/11.98  thf('154', plain,
% 11.79/11.98      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['30', '33'])).
% 11.79/11.98  thf('155', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 11.79/11.98         <= ((![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['106', '107'])).
% 11.79/11.98  thf('156', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['154', '155'])).
% 11.79/11.98  thf('157', plain,
% 11.79/11.98      ((((r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 11.79/11.98             = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['153', '156'])).
% 11.79/11.98  thf('158', plain,
% 11.79/11.98      (![X28 : $i, X29 : $i]:
% 11.79/11.98         (~ (v1_relat_1 @ X28)
% 11.79/11.98          | ~ (v1_funct_1 @ X28)
% 11.79/11.98          | ((k1_funct_1 @ X29 @ (sk_C_1 @ X28 @ X29))
% 11.79/11.98              != (k1_funct_1 @ X28 @ (sk_C_1 @ X28 @ X29)))
% 11.79/11.98          | (r1_partfun1 @ X29 @ X28)
% 11.79/11.98          | ~ (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 11.79/11.98          | ~ (v1_funct_1 @ X29)
% 11.79/11.98          | ~ (v1_relat_1 @ X29))),
% 11.79/11.98      inference('cnf', [status(esa)], [t132_partfun1])).
% 11.79/11.98  thf('159', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 11.79/11.98           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_C_2)
% 11.79/11.98         | ~ (v1_funct_1 @ sk_C_2)
% 11.79/11.98         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_2) @ (k1_relat_1 @ sk_D))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | ~ (v1_funct_1 @ sk_D)
% 11.79/11.98         | ~ (v1_relat_1 @ sk_D)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['157', '158'])).
% 11.79/11.98  thf('160', plain, ((v1_relat_1 @ sk_C_2)),
% 11.79/11.98      inference('sup-', [status(thm)], ['38', '39'])).
% 11.79/11.98  thf('161', plain, ((v1_funct_1 @ sk_C_2)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('162', plain,
% 11.79/11.98      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['30', '33'])).
% 11.79/11.98  thf('163', plain,
% 11.79/11.98      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 11.79/11.98      inference('demod', [status(thm)], ['133', '139'])).
% 11.79/11.98  thf('164', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 11.79/11.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.79/11.98  thf('165', plain, ((v1_funct_1 @ sk_D)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('166', plain, ((v1_relat_1 @ sk_D)),
% 11.79/11.98      inference('sup-', [status(thm)], ['47', '48'])).
% 11.79/11.98  thf('167', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 11.79/11.98           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98         | (r1_partfun1 @ sk_C_2 @ sk_D)))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('demod', [status(thm)],
% 11.79/11.98                ['159', '160', '161', '162', '163', '164', '165', '166'])).
% 11.79/11.98  thf('168', plain,
% 11.79/11.98      (((r1_partfun1 @ sk_C_2 @ sk_D))
% 11.79/11.98         <= ((((sk_A) = (k1_xboole_0))) & 
% 11.79/11.98             (![X31 : $i]:
% 11.79/11.98                (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98                 | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))))),
% 11.79/11.98      inference('simplify', [status(thm)], ['167'])).
% 11.79/11.98  thf('169', plain,
% 11.79/11.98      ((~ (r1_partfun1 @ sk_C_2 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 11.79/11.98      inference('split', [status(esa)], ['51'])).
% 11.79/11.98  thf('170', plain,
% 11.79/11.98      (~ (((sk_A) = (k1_xboole_0))) | 
% 11.79/11.98       ~
% 11.79/11.98       (![X31 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))) | 
% 11.79/11.98       ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('sup-', [status(thm)], ['168', '169'])).
% 11.79/11.98  thf('171', plain,
% 11.79/11.98      ((![X31 : $i]:
% 11.79/11.98          (~ (r2_hidden @ X31 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X31) = (k1_funct_1 @ sk_D @ X31)))) | 
% 11.79/11.98       ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('split', [status(esa)], ['0'])).
% 11.79/11.98  thf('172', plain,
% 11.79/11.98      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 11.79/11.98       ~ ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 11.79/11.98      inference('split', [status(esa)], ['5'])).
% 11.79/11.98  thf('173', plain,
% 11.79/11.98      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_2)))
% 11.79/11.98         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup+', [status(thm)], ['4', '6'])).
% 11.79/11.98  thf('174', plain,
% 11.79/11.98      (((r1_partfun1 @ sk_C_2 @ sk_D)) <= (((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 11.79/11.98      inference('split', [status(esa)], ['0'])).
% 11.79/11.98  thf('175', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 11.79/11.98      inference('simplify', [status(thm)], ['66'])).
% 11.79/11.98  thf('176', plain,
% 11.79/11.98      (![X20 : $i, X21 : $i]:
% 11.79/11.98         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 11.79/11.98  thf('177', plain,
% 11.79/11.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['72', '73'])).
% 11.79/11.98  thf('178', plain,
% 11.79/11.98      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 11.79/11.98      inference('sup-', [status(thm)], ['176', '177'])).
% 11.79/11.98  thf('179', plain,
% 11.79/11.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.79/11.98      inference('demod', [status(thm)], ['78', '81'])).
% 11.79/11.98  thf('180', plain,
% 11.79/11.98      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['178', '179'])).
% 11.79/11.98  thf('181', plain,
% 11.79/11.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 11.79/11.98         (~ (v1_relat_1 @ X28)
% 11.79/11.98          | ~ (v1_funct_1 @ X28)
% 11.79/11.98          | ~ (r1_partfun1 @ X29 @ X28)
% 11.79/11.98          | ((k1_funct_1 @ X29 @ X30) = (k1_funct_1 @ X28 @ X30))
% 11.79/11.98          | ~ (r2_hidden @ X30 @ (k1_relat_1 @ X29))
% 11.79/11.98          | ~ (r1_tarski @ (k1_relat_1 @ X29) @ (k1_relat_1 @ X28))
% 11.79/11.98          | ~ (v1_funct_1 @ X29)
% 11.79/11.98          | ~ (v1_relat_1 @ X29))),
% 11.79/11.98      inference('cnf', [status(esa)], [t132_partfun1])).
% 11.79/11.98  thf('182', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i]:
% 11.79/11.98         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 11.79/11.98          | ((sk_B) = (k1_xboole_0))
% 11.79/11.98          | ~ (v1_relat_1 @ X0)
% 11.79/11.98          | ~ (v1_funct_1 @ X0)
% 11.79/11.98          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 11.79/11.98          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 11.79/11.98          | ~ (r1_partfun1 @ X0 @ sk_D)
% 11.79/11.98          | ~ (v1_funct_1 @ sk_D)
% 11.79/11.98          | ~ (v1_relat_1 @ sk_D))),
% 11.79/11.98      inference('sup-', [status(thm)], ['180', '181'])).
% 11.79/11.98  thf('183', plain, ((v1_funct_1 @ sk_D)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('184', plain, ((v1_relat_1 @ sk_D)),
% 11.79/11.98      inference('sup-', [status(thm)], ['47', '48'])).
% 11.79/11.98  thf('185', plain,
% 11.79/11.98      (![X0 : $i, X1 : $i]:
% 11.79/11.98         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 11.79/11.98          | ((sk_B) = (k1_xboole_0))
% 11.79/11.98          | ~ (v1_relat_1 @ X0)
% 11.79/11.98          | ~ (v1_funct_1 @ X0)
% 11.79/11.98          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 11.79/11.98          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 11.79/11.98          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 11.79/11.98      inference('demod', [status(thm)], ['182', '183', '184'])).
% 11.79/11.98  thf('186', plain,
% 11.79/11.98      (![X0 : $i]:
% 11.79/11.98         (~ (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98          | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 11.79/11.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98          | ~ (v1_funct_1 @ sk_C_2)
% 11.79/11.98          | ~ (v1_relat_1 @ sk_C_2)
% 11.79/11.98          | ((sk_B) = (k1_xboole_0)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['175', '185'])).
% 11.79/11.98  thf('187', plain, ((v1_funct_1 @ sk_C_2)),
% 11.79/11.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.79/11.98  thf('188', plain, ((v1_relat_1 @ sk_C_2)),
% 11.79/11.98      inference('sup-', [status(thm)], ['38', '39'])).
% 11.79/11.98  thf('189', plain,
% 11.79/11.98      (![X0 : $i]:
% 11.79/11.98         (~ (r1_partfun1 @ sk_C_2 @ sk_D)
% 11.79/11.98          | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 11.79/11.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98          | ((sk_B) = (k1_xboole_0)))),
% 11.79/11.98      inference('demod', [status(thm)], ['186', '187', '188'])).
% 11.79/11.98  thf('190', plain,
% 11.79/11.98      ((![X0 : $i]:
% 11.79/11.98          (((sk_B) = (k1_xboole_0))
% 11.79/11.98           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 11.79/11.98           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 11.79/11.98         <= (((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 11.79/11.98      inference('sup-', [status(thm)], ['174', '189'])).
% 11.79/11.98  thf('191', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))
% 11.79/11.98         | ((sk_B) = (k1_xboole_0))))
% 11.79/11.98         <= (((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['173', '190'])).
% 11.79/11.98  thf('192', plain,
% 11.79/11.98      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 11.79/11.98         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 11.79/11.98      inference('split', [status(esa)], ['51'])).
% 11.79/11.98  thf('193', plain,
% 11.79/11.98      (((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 11.79/11.98         | ((sk_B) = (k1_xboole_0))))
% 11.79/11.98         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 11.79/11.98             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['191', '192'])).
% 11.79/11.98  thf('194', plain,
% 11.79/11.98      ((((sk_B) = (k1_xboole_0)))
% 11.79/11.98         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 11.79/11.98             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('simplify', [status(thm)], ['193'])).
% 11.79/11.98  thf('195', plain,
% 11.79/11.98      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 11.79/11.98      inference('split', [status(esa)], ['8'])).
% 11.79/11.98  thf('196', plain,
% 11.79/11.98      ((((k1_xboole_0) != (k1_xboole_0)))
% 11.79/11.98         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 11.79/11.98             ~ (((sk_B) = (k1_xboole_0))) & 
% 11.79/11.98             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 11.79/11.98             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 11.79/11.98      inference('sup-', [status(thm)], ['194', '195'])).
% 11.79/11.98  thf('197', plain,
% 11.79/11.98      ((((sk_B) = (k1_xboole_0))) | 
% 11.79/11.98       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 11.79/11.98       ~ ((r1_partfun1 @ sk_C_2 @ sk_D)) | 
% 11.79/11.98       (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 11.79/11.98      inference('simplify', [status(thm)], ['196'])).
% 11.79/11.98  thf('198', plain,
% 11.79/11.98      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 11.79/11.98      inference('split', [status(esa)], ['8'])).
% 11.79/11.98  thf('199', plain, ($false),
% 11.79/11.98      inference('sat_resolution*', [status(thm)],
% 11.79/11.98                ['54', '55', '121', '170', '171', '172', '197', '198'])).
% 11.79/11.98  
% 11.79/11.98  % SZS output end Refutation
% 11.79/11.98  
% 11.82/11.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
