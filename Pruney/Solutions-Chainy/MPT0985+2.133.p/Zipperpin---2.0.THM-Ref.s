%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X0mfgjYBCj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:45 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  196 (4703 expanded)
%              Number of leaves         :   33 (1363 expanded)
%              Depth                    :   25
%              Number of atoms          : 1711 (77869 expanded)
%              Number of equality atoms :  109 (3512 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('26',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X27: $i] :
      ( ( v1_funct_2 @ X27 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('53',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('55',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('60',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('62',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','70'])).

thf('72',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('74',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','57','74'])).

thf('76',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('79',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('87',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('88',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('89',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ k1_xboole_0 )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('93',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('94',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('97',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','95','96'])).

thf('98',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','97'])).

thf('99',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('102',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('108',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('112',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['110','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('117',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','106','109'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['75','118'])).

thf('120',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('121',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','119','120'])).

thf('122',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('124',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('138',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['137','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('150',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('152',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('154',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','119','120'])).

thf('156',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','156','157','158','159'])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['122','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X0mfgjYBCj
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.03/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.03/1.31  % Solved by: fo/fo7.sh
% 1.03/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.31  % done 1064 iterations in 0.850s
% 1.03/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.03/1.31  % SZS output start Refutation
% 1.03/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.31  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.03/1.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.03/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.31  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.03/1.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.31  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.03/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.31  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.31  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.03/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.03/1.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.31  thf(t31_funct_2, conjecture,
% 1.03/1.31    (![A:$i,B:$i,C:$i]:
% 1.03/1.31     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.03/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.31       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.03/1.31         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.03/1.31           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.03/1.31           ( m1_subset_1 @
% 1.03/1.31             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.03/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.31    (~( ![A:$i,B:$i,C:$i]:
% 1.03/1.31        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.03/1.31            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.31          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.03/1.31            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.03/1.31              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.03/1.31              ( m1_subset_1 @
% 1.03/1.31                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.03/1.31    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.03/1.31  thf('0', plain,
% 1.03/1.31      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.03/1.31        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.03/1.31        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('1', plain,
% 1.03/1.31      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.03/1.31         <= (~
% 1.03/1.31             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.31               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.31      inference('split', [status(esa)], ['0'])).
% 1.03/1.31  thf('2', plain,
% 1.03/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf(cc1_relset_1, axiom,
% 1.03/1.31    (![A:$i,B:$i,C:$i]:
% 1.03/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.31       ( v1_relat_1 @ C ) ))).
% 1.03/1.31  thf('3', plain,
% 1.03/1.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.03/1.31         ((v1_relat_1 @ X10)
% 1.03/1.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.03/1.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.31  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.31  thf(dt_k2_funct_1, axiom,
% 1.03/1.31    (![A:$i]:
% 1.03/1.31     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.31       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.03/1.31         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.03/1.31  thf('5', plain,
% 1.03/1.31      (![X8 : $i]:
% 1.03/1.31         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.03/1.31          | ~ (v1_funct_1 @ X8)
% 1.03/1.31          | ~ (v1_relat_1 @ X8))),
% 1.03/1.31      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.31  thf('6', plain,
% 1.03/1.31      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.03/1.31         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.03/1.31      inference('split', [status(esa)], ['0'])).
% 1.03/1.31  thf('7', plain,
% 1.03/1.31      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.03/1.31         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.03/1.31      inference('sup-', [status(thm)], ['5', '6'])).
% 1.03/1.31  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('9', plain,
% 1.03/1.31      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.03/1.31      inference('demod', [status(thm)], ['7', '8'])).
% 1.03/1.31  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['4', '9'])).
% 1.03/1.31  thf('11', plain,
% 1.03/1.31      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('split', [status(esa)], ['0'])).
% 1.03/1.31  thf(d1_funct_2, axiom,
% 1.03/1.31    (![A:$i,B:$i,C:$i]:
% 1.03/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.31       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.31           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.03/1.31             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.03/1.31         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.31           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.03/1.31             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.03/1.31  thf(zf_stmt_1, axiom,
% 1.03/1.31    (![B:$i,A:$i]:
% 1.03/1.31     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.31       ( zip_tseitin_0 @ B @ A ) ))).
% 1.03/1.31  thf('12', plain,
% 1.03/1.31      (![X19 : $i, X20 : $i]:
% 1.03/1.31         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.31  thf('13', plain,
% 1.03/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.03/1.31  thf(zf_stmt_3, axiom,
% 1.03/1.31    (![C:$i,B:$i,A:$i]:
% 1.03/1.31     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.03/1.31       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.31  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.03/1.31  thf(zf_stmt_5, axiom,
% 1.03/1.31    (![A:$i,B:$i,C:$i]:
% 1.03/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.31       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.03/1.31         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.31           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.31             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.03/1.31  thf('14', plain,
% 1.03/1.31      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.03/1.31         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.03/1.31          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.03/1.31          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.31  thf('15', plain,
% 1.03/1.31      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.03/1.31      inference('sup-', [status(thm)], ['13', '14'])).
% 1.03/1.31  thf('16', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.03/1.31      inference('sup-', [status(thm)], ['12', '15'])).
% 1.03/1.31  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('18', plain,
% 1.03/1.31      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.03/1.31         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.03/1.31          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 1.03/1.31          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.03/1.31  thf('19', plain,
% 1.03/1.31      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.03/1.31        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['17', '18'])).
% 1.03/1.31  thf('20', plain,
% 1.03/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf(redefinition_k1_relset_1, axiom,
% 1.03/1.31    (![A:$i,B:$i,C:$i]:
% 1.03/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.31       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.03/1.31  thf('21', plain,
% 1.03/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.31         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.03/1.31          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.03/1.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.31  thf('22', plain,
% 1.03/1.31      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.03/1.31      inference('sup-', [status(thm)], ['20', '21'])).
% 1.03/1.31  thf('23', plain,
% 1.03/1.31      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.03/1.31      inference('demod', [status(thm)], ['19', '22'])).
% 1.03/1.31  thf('24', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['16', '23'])).
% 1.03/1.31  thf(t55_funct_1, axiom,
% 1.03/1.31    (![A:$i]:
% 1.03/1.31     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.31       ( ( v2_funct_1 @ A ) =>
% 1.03/1.31         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.03/1.31           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.03/1.31  thf('25', plain,
% 1.03/1.31      (![X9 : $i]:
% 1.03/1.31         (~ (v2_funct_1 @ X9)
% 1.03/1.31          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 1.03/1.31          | ~ (v1_funct_1 @ X9)
% 1.03/1.31          | ~ (v1_relat_1 @ X9))),
% 1.03/1.31      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.31  thf('26', plain,
% 1.03/1.31      (![X8 : $i]:
% 1.03/1.31         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.03/1.31          | ~ (v1_funct_1 @ X8)
% 1.03/1.31          | ~ (v1_relat_1 @ X8))),
% 1.03/1.31      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.31  thf('27', plain,
% 1.03/1.31      (![X8 : $i]:
% 1.03/1.31         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.03/1.31          | ~ (v1_funct_1 @ X8)
% 1.03/1.31          | ~ (v1_relat_1 @ X8))),
% 1.03/1.31      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.31  thf('28', plain,
% 1.03/1.31      (![X9 : $i]:
% 1.03/1.31         (~ (v2_funct_1 @ X9)
% 1.03/1.31          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.03/1.31          | ~ (v1_funct_1 @ X9)
% 1.03/1.31          | ~ (v1_relat_1 @ X9))),
% 1.03/1.31      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.31  thf(t3_funct_2, axiom,
% 1.03/1.31    (![A:$i]:
% 1.03/1.31     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.31       ( ( v1_funct_1 @ A ) & 
% 1.03/1.31         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.03/1.31         ( m1_subset_1 @
% 1.03/1.31           A @ 
% 1.03/1.31           ( k1_zfmisc_1 @
% 1.03/1.31             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.03/1.31  thf('29', plain,
% 1.03/1.31      (![X27 : $i]:
% 1.03/1.31         ((v1_funct_2 @ X27 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27))
% 1.03/1.31          | ~ (v1_funct_1 @ X27)
% 1.03/1.31          | ~ (v1_relat_1 @ X27))),
% 1.03/1.31      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.03/1.31  thf('30', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.03/1.31          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.03/1.31      inference('sup+', [status(thm)], ['28', '29'])).
% 1.03/1.31  thf('31', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         (~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.03/1.31      inference('sup-', [status(thm)], ['27', '30'])).
% 1.03/1.31  thf('32', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0))),
% 1.03/1.31      inference('simplify', [status(thm)], ['31'])).
% 1.03/1.31  thf('33', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         (~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.03/1.31      inference('sup-', [status(thm)], ['26', '32'])).
% 1.03/1.31  thf('34', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0))),
% 1.03/1.31      inference('simplify', [status(thm)], ['33'])).
% 1.03/1.31  thf('35', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31           (k1_relat_1 @ X0))
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v2_funct_1 @ X0))),
% 1.03/1.31      inference('sup+', [status(thm)], ['25', '34'])).
% 1.03/1.31  thf('36', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         (~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31             (k1_relat_1 @ X0)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['35'])).
% 1.03/1.31  thf('37', plain,
% 1.03/1.31      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.03/1.31        | ((sk_B) = (k1_xboole_0))
% 1.03/1.31        | ~ (v1_relat_1 @ sk_C)
% 1.03/1.31        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.31        | ~ (v2_funct_1 @ sk_C))),
% 1.03/1.31      inference('sup+', [status(thm)], ['24', '36'])).
% 1.03/1.31  thf('38', plain,
% 1.03/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf(redefinition_k2_relset_1, axiom,
% 1.03/1.31    (![A:$i,B:$i,C:$i]:
% 1.03/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.31       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.03/1.31  thf('39', plain,
% 1.03/1.31      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.03/1.31         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.03/1.31          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.03/1.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.31  thf('40', plain,
% 1.03/1.31      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.03/1.31      inference('sup-', [status(thm)], ['38', '39'])).
% 1.03/1.31  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.03/1.31      inference('sup+', [status(thm)], ['40', '41'])).
% 1.03/1.31  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.31  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('46', plain,
% 1.03/1.31      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.03/1.31        | ((sk_B) = (k1_xboole_0)))),
% 1.03/1.31      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 1.03/1.31  thf('47', plain,
% 1.03/1.31      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('split', [status(esa)], ['0'])).
% 1.03/1.31  thf('48', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.03/1.31  thf('49', plain,
% 1.03/1.31      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['11', '48'])).
% 1.03/1.31  thf('50', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.03/1.31  thf('51', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.03/1.31      inference('sup+', [status(thm)], ['40', '41'])).
% 1.03/1.31  thf(t64_relat_1, axiom,
% 1.03/1.31    (![A:$i]:
% 1.03/1.31     ( ( v1_relat_1 @ A ) =>
% 1.03/1.31       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.31           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.31         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.03/1.31  thf('52', plain,
% 1.03/1.31      (![X7 : $i]:
% 1.03/1.31         (((k2_relat_1 @ X7) != (k1_xboole_0))
% 1.03/1.31          | ((X7) = (k1_xboole_0))
% 1.03/1.31          | ~ (v1_relat_1 @ X7))),
% 1.03/1.31      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.03/1.31  thf('53', plain,
% 1.03/1.31      ((((sk_B) != (k1_xboole_0))
% 1.03/1.31        | ~ (v1_relat_1 @ sk_C)
% 1.03/1.31        | ((sk_C) = (k1_xboole_0)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['51', '52'])).
% 1.03/1.31  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.31  thf('55', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 1.03/1.31      inference('demod', [status(thm)], ['53', '54'])).
% 1.03/1.31  thf('56', plain,
% 1.03/1.31      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['50', '55'])).
% 1.03/1.31  thf('57', plain,
% 1.03/1.31      ((((sk_C) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['56'])).
% 1.03/1.31  thf('58', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.03/1.31  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.03/1.31      inference('sup+', [status(thm)], ['40', '41'])).
% 1.03/1.31  thf('60', plain,
% 1.03/1.31      (![X8 : $i]:
% 1.03/1.31         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.03/1.31          | ~ (v1_funct_1 @ X8)
% 1.03/1.31          | ~ (v1_relat_1 @ X8))),
% 1.03/1.31      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.31  thf('61', plain,
% 1.03/1.31      (![X9 : $i]:
% 1.03/1.31         (~ (v2_funct_1 @ X9)
% 1.03/1.31          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.03/1.31          | ~ (v1_funct_1 @ X9)
% 1.03/1.31          | ~ (v1_relat_1 @ X9))),
% 1.03/1.31      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.31  thf('62', plain,
% 1.03/1.31      (![X7 : $i]:
% 1.03/1.31         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 1.03/1.31          | ((X7) = (k1_xboole_0))
% 1.03/1.31          | ~ (v1_relat_1 @ X7))),
% 1.03/1.31      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.03/1.31  thf('63', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.03/1.31          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['61', '62'])).
% 1.03/1.31  thf('64', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         (~ (v1_relat_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0)
% 1.03/1.31          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['60', '63'])).
% 1.03/1.31  thf('65', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0))),
% 1.03/1.31      inference('simplify', [status(thm)], ['64'])).
% 1.03/1.31  thf('66', plain,
% 1.03/1.31      ((((sk_B) != (k1_xboole_0))
% 1.03/1.31        | ~ (v1_relat_1 @ sk_C)
% 1.03/1.31        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.31        | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 1.03/1.31        | ~ (v2_funct_1 @ sk_C))),
% 1.03/1.31      inference('sup-', [status(thm)], ['59', '65'])).
% 1.03/1.31  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.31  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('70', plain,
% 1.03/1.31      ((((sk_B) != (k1_xboole_0)) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 1.03/1.31      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 1.03/1.31  thf('71', plain,
% 1.03/1.31      (((((k1_xboole_0) != (k1_xboole_0))
% 1.03/1.31         | ((k2_funct_1 @ sk_C) = (k1_xboole_0))))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['58', '70'])).
% 1.03/1.31  thf('72', plain,
% 1.03/1.31      ((((k2_funct_1 @ sk_C) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['71'])).
% 1.03/1.31  thf('73', plain,
% 1.03/1.31      ((((sk_C) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['56'])).
% 1.03/1.31  thf('74', plain,
% 1.03/1.31      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['72', '73'])).
% 1.03/1.31  thf('75', plain,
% 1.03/1.31      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['49', '57', '74'])).
% 1.03/1.31  thf('76', plain,
% 1.03/1.31      ((((sk_C) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['56'])).
% 1.03/1.31  thf('77', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.03/1.31      inference('sup+', [status(thm)], ['40', '41'])).
% 1.03/1.31  thf('78', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.31           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.03/1.31          | ~ (v2_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_funct_1 @ X0)
% 1.03/1.31          | ~ (v1_relat_1 @ X0))),
% 1.03/1.31      inference('simplify', [status(thm)], ['33'])).
% 1.03/1.31  thf('79', plain,
% 1.03/1.31      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.03/1.31         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.03/1.31        | ~ (v1_relat_1 @ sk_C)
% 1.03/1.31        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.31        | ~ (v2_funct_1 @ sk_C))),
% 1.03/1.31      inference('sup+', [status(thm)], ['77', '78'])).
% 1.03/1.31  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.31  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('83', plain,
% 1.03/1.31      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 1.03/1.31        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.03/1.31      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 1.03/1.31  thf('84', plain,
% 1.03/1.31      (((v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ sk_B @ 
% 1.03/1.31         (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup+', [status(thm)], ['76', '83'])).
% 1.03/1.31  thf('85', plain,
% 1.03/1.31      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['72', '73'])).
% 1.03/1.31  thf('86', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.03/1.31  thf('87', plain,
% 1.03/1.31      ((((sk_C) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['56'])).
% 1.03/1.31  thf('88', plain,
% 1.03/1.31      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['72', '73'])).
% 1.03/1.31  thf('89', plain,
% 1.03/1.31      ((((sk_C) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['56'])).
% 1.03/1.31  thf('90', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.31  thf('91', plain,
% 1.03/1.31      ((((k2_relset_1 @ sk_A @ sk_B @ k1_xboole_0) = (sk_B)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup+', [status(thm)], ['89', '90'])).
% 1.03/1.31  thf('92', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.03/1.31  thf(t4_subset_1, axiom,
% 1.03/1.31    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.03/1.31  thf('93', plain,
% 1.03/1.31      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 1.03/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.03/1.31  thf('94', plain,
% 1.03/1.31      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.03/1.31         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.03/1.31          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.03/1.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.31  thf('95', plain,
% 1.03/1.31      (![X0 : $i, X1 : $i]:
% 1.03/1.31         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 1.03/1.31      inference('sup-', [status(thm)], ['93', '94'])).
% 1.03/1.31  thf('96', plain,
% 1.03/1.31      ((((sk_B) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.03/1.31  thf('97', plain,
% 1.03/1.31      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['91', '92', '95', '96'])).
% 1.03/1.31  thf('98', plain,
% 1.03/1.31      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['84', '85', '86', '87', '88', '97'])).
% 1.03/1.31  thf('99', plain,
% 1.03/1.31      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.03/1.31         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.03/1.31          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 1.03/1.31          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.03/1.31  thf('100', plain,
% 1.03/1.31      (((~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.03/1.31         | ((k1_xboole_0)
% 1.03/1.31             = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['98', '99'])).
% 1.03/1.31  thf('101', plain,
% 1.03/1.31      (![X19 : $i, X20 : $i]:
% 1.03/1.31         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.31  thf('102', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 1.03/1.31      inference('simplify', [status(thm)], ['101'])).
% 1.03/1.31  thf('103', plain,
% 1.03/1.31      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 1.03/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.03/1.31  thf('104', plain,
% 1.03/1.31      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.03/1.31         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.03/1.31          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.03/1.31          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.31  thf('105', plain,
% 1.03/1.31      (![X0 : $i, X1 : $i]:
% 1.03/1.31         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.03/1.31      inference('sup-', [status(thm)], ['103', '104'])).
% 1.03/1.31  thf('106', plain,
% 1.03/1.31      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.03/1.31      inference('sup-', [status(thm)], ['102', '105'])).
% 1.03/1.31  thf('107', plain,
% 1.03/1.31      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 1.03/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.03/1.31  thf('108', plain,
% 1.03/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.31         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.03/1.31          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.03/1.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.31  thf('109', plain,
% 1.03/1.31      (![X0 : $i, X1 : $i]:
% 1.03/1.31         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.03/1.31      inference('sup-', [status(thm)], ['107', '108'])).
% 1.03/1.31  thf('110', plain,
% 1.03/1.31      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['100', '106', '109'])).
% 1.03/1.31  thf('111', plain,
% 1.03/1.31      (![X0 : $i, X1 : $i]:
% 1.03/1.31         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.03/1.31      inference('sup-', [status(thm)], ['107', '108'])).
% 1.03/1.31  thf('112', plain,
% 1.03/1.31      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.03/1.31         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 1.03/1.31          | (v1_funct_2 @ X23 @ X21 @ X22)
% 1.03/1.31          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.03/1.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.03/1.31  thf('113', plain,
% 1.03/1.31      (![X0 : $i, X1 : $i]:
% 1.03/1.31         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 1.03/1.31          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.03/1.31          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.03/1.31      inference('sup-', [status(thm)], ['111', '112'])).
% 1.03/1.31  thf('114', plain,
% 1.03/1.31      (![X0 : $i]:
% 1.03/1.31         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 1.03/1.31          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 1.03/1.31      inference('simplify', [status(thm)], ['113'])).
% 1.03/1.31  thf('115', plain,
% 1.03/1.31      ((![X0 : $i]:
% 1.03/1.31          (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.03/1.31           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('sup-', [status(thm)], ['110', '114'])).
% 1.03/1.31  thf('116', plain,
% 1.03/1.31      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.03/1.31      inference('sup-', [status(thm)], ['102', '105'])).
% 1.03/1.31  thf('117', plain,
% 1.03/1.31      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['100', '106', '109'])).
% 1.03/1.31  thf('118', plain,
% 1.03/1.31      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 1.03/1.31         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.03/1.31      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.03/1.31  thf('119', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.03/1.31      inference('demod', [status(thm)], ['75', '118'])).
% 1.03/1.31  thf('120', plain,
% 1.03/1.31      (~
% 1.03/1.31       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.31         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.03/1.31       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.03/1.31       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.03/1.31      inference('split', [status(esa)], ['0'])).
% 1.03/1.31  thf('121', plain,
% 1.03/1.31      (~
% 1.03/1.31       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.31         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.03/1.31      inference('sat_resolution*', [status(thm)], ['10', '119', '120'])).
% 1.03/1.31  thf('122', plain,
% 1.03/1.31      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.03/1.31      inference('simpl_trail', [status(thm)], ['1', '121'])).
% 1.03/1.31  thf('123', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.03/1.31      inference('sup+', [status(thm)], ['40', '41'])).
% 1.03/1.31  thf('124', plain,
% 1.03/1.31      (![X9 : $i]:
% 1.03/1.31         (~ (v2_funct_1 @ X9)
% 1.03/1.31          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 1.03/1.31          | ~ (v1_funct_1 @ X9)
% 1.03/1.31          | ~ (v1_relat_1 @ X9))),
% 1.03/1.31      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.31  thf('125', plain,
% 1.03/1.31      (![X8 : $i]:
% 1.03/1.31         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.03/1.31          | ~ (v1_funct_1 @ X8)
% 1.03/1.31          | ~ (v1_relat_1 @ X8))),
% 1.03/1.31      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.31  thf('126', plain,
% 1.03/1.31      (![X8 : $i]:
% 1.03/1.31         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.03/1.31          | ~ (v1_funct_1 @ X8)
% 1.03/1.31          | ~ (v1_relat_1 @ X8))),
% 1.03/1.31      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.03/1.31  thf('127', plain,
% 1.03/1.31      (![X9 : $i]:
% 1.03/1.31         (~ (v2_funct_1 @ X9)
% 1.03/1.31          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.03/1.31          | ~ (v1_funct_1 @ X9)
% 1.03/1.31          | ~ (v1_relat_1 @ X9))),
% 1.03/1.31      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.31  thf('128', plain,
% 1.03/1.31      (![X27 : $i]:
% 1.03/1.31         ((m1_subset_1 @ X27 @ 
% 1.03/1.31           (k1_zfmisc_1 @ 
% 1.03/1.31            (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27))))
% 1.03/1.31          | ~ (v1_funct_1 @ X27)
% 1.03/1.31          | ~ (v1_relat_1 @ X27))),
% 1.03/1.32      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.03/1.32  thf('129', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32           (k1_zfmisc_1 @ 
% 1.03/1.32            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.03/1.32          | ~ (v1_relat_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.03/1.32          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.03/1.32      inference('sup+', [status(thm)], ['127', '128'])).
% 1.03/1.32  thf('130', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         (~ (v1_relat_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0)
% 1.03/1.32          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32             (k1_zfmisc_1 @ 
% 1.03/1.32              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.03/1.32               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.03/1.32      inference('sup-', [status(thm)], ['126', '129'])).
% 1.03/1.32  thf('131', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32           (k1_zfmisc_1 @ 
% 1.03/1.32            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0))),
% 1.03/1.32      inference('simplify', [status(thm)], ['130'])).
% 1.03/1.32  thf('132', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         (~ (v1_relat_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32             (k1_zfmisc_1 @ 
% 1.03/1.32              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.03/1.32               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.03/1.32      inference('sup-', [status(thm)], ['125', '131'])).
% 1.03/1.32  thf('133', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32           (k1_zfmisc_1 @ 
% 1.03/1.32            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0))),
% 1.03/1.32      inference('simplify', [status(thm)], ['132'])).
% 1.03/1.32  thf('134', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.03/1.32          | ~ (v1_relat_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v2_funct_1 @ X0))),
% 1.03/1.32      inference('sup+', [status(thm)], ['124', '133'])).
% 1.03/1.32  thf('135', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         (~ (v2_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0)
% 1.03/1.32          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.03/1.32             (k1_zfmisc_1 @ 
% 1.03/1.32              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.03/1.32      inference('simplify', [status(thm)], ['134'])).
% 1.03/1.32  thf('136', plain,
% 1.03/1.32      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 1.03/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.03/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.03/1.32      inference('sup+', [status(thm)], ['123', '135'])).
% 1.03/1.32  thf('137', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.03/1.32      inference('sup+', [status(thm)], ['40', '41'])).
% 1.03/1.32  thf('138', plain,
% 1.03/1.32      (![X19 : $i, X20 : $i]:
% 1.03/1.32         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 1.03/1.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.32  thf('139', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.03/1.32          | ~ (v2_funct_1 @ X0)
% 1.03/1.32          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 1.03/1.32          | ~ (v1_funct_1 @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ X0))),
% 1.03/1.32      inference('simplify', [status(thm)], ['64'])).
% 1.03/1.32  thf('140', plain,
% 1.03/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.32         (((k2_relat_1 @ X1) != (X0))
% 1.03/1.32          | (zip_tseitin_0 @ X0 @ X2)
% 1.03/1.32          | ~ (v1_relat_1 @ X1)
% 1.03/1.32          | ~ (v1_funct_1 @ X1)
% 1.03/1.32          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.03/1.32          | ~ (v2_funct_1 @ X1))),
% 1.03/1.32      inference('sup-', [status(thm)], ['138', '139'])).
% 1.03/1.32  thf('141', plain,
% 1.03/1.32      (![X1 : $i, X2 : $i]:
% 1.03/1.32         (~ (v2_funct_1 @ X1)
% 1.03/1.32          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 1.03/1.32          | ~ (v1_funct_1 @ X1)
% 1.03/1.32          | ~ (v1_relat_1 @ X1)
% 1.03/1.32          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 1.03/1.32      inference('simplify', [status(thm)], ['140'])).
% 1.03/1.32  thf('142', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         ((zip_tseitin_0 @ sk_B @ X0)
% 1.03/1.32          | ~ (v1_relat_1 @ sk_C)
% 1.03/1.32          | ~ (v1_funct_1 @ sk_C)
% 1.03/1.32          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 1.03/1.32          | ~ (v2_funct_1 @ sk_C))),
% 1.03/1.32      inference('sup+', [status(thm)], ['137', '141'])).
% 1.03/1.32  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.32      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.32  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.32  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.32  thf('146', plain,
% 1.03/1.32      (![X0 : $i]:
% 1.03/1.32         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 1.03/1.32      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 1.03/1.32  thf('147', plain,
% 1.03/1.32      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.03/1.32         <= (~
% 1.03/1.32             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.32      inference('split', [status(esa)], ['0'])).
% 1.03/1.32  thf('148', plain,
% 1.03/1.32      ((![X0 : $i]:
% 1.03/1.32          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.03/1.32              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.03/1.32           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.03/1.32         <= (~
% 1.03/1.32             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.32      inference('sup-', [status(thm)], ['146', '147'])).
% 1.03/1.32  thf('149', plain,
% 1.03/1.32      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 1.03/1.32      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.03/1.32  thf('150', plain,
% 1.03/1.32      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.03/1.32         <= (~
% 1.03/1.32             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.32      inference('demod', [status(thm)], ['148', '149'])).
% 1.03/1.32  thf('151', plain,
% 1.03/1.32      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.03/1.32      inference('sup-', [status(thm)], ['13', '14'])).
% 1.03/1.32  thf('152', plain,
% 1.03/1.32      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 1.03/1.32         <= (~
% 1.03/1.32             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.32      inference('sup-', [status(thm)], ['150', '151'])).
% 1.03/1.32  thf('153', plain,
% 1.03/1.32      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.03/1.32      inference('demod', [status(thm)], ['19', '22'])).
% 1.03/1.32  thf('154', plain,
% 1.03/1.32      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.03/1.32         <= (~
% 1.03/1.32             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.03/1.32      inference('sup-', [status(thm)], ['152', '153'])).
% 1.03/1.32  thf('155', plain,
% 1.03/1.32      (~
% 1.03/1.32       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.03/1.32      inference('sat_resolution*', [status(thm)], ['10', '119', '120'])).
% 1.03/1.32  thf('156', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.03/1.32      inference('simpl_trail', [status(thm)], ['154', '155'])).
% 1.03/1.32  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.32      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.32  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.32  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.32  thf('160', plain,
% 1.03/1.32      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.03/1.32      inference('demod', [status(thm)], ['136', '156', '157', '158', '159'])).
% 1.03/1.32  thf('161', plain, ($false), inference('demod', [status(thm)], ['122', '160'])).
% 1.03/1.32  
% 1.03/1.32  % SZS output end Refutation
% 1.03/1.32  
% 1.03/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
