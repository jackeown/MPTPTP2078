%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0sq0g2uLJB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:41 EST 2020

% Result     : Theorem 18.76s
% Output     : Refutation 18.76s
% Verified   : 
% Statistics : Number of formulae       :  272 (1529 expanded)
%              Number of leaves         :   39 ( 471 expanded)
%              Depth                    :   30
%              Number of atoms          : 2282 (21646 expanded)
%              Number of equality atoms :  138 ( 925 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('60',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X6 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('72',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('87',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X6 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('93',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','97'])).

thf('99',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','98'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('105',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','105'])).

thf('107',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('108',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('110',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['69','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('116',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('120',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','122'])).

thf('124',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('125',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['113','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('134',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ X2 )
      | ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['132','136'])).

thf('138',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('139',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('141',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B = X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('148',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('149',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['139','151'])).

thf('153',plain,
    ( ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','153'])).

thf('155',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','154'])).

thf('156',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('157',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('160',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('161',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('163',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('166',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('167',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('172',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','172'])).

thf('174',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['163','173'])).

thf('175',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('176',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('178',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['158','178'])).

thf('180',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('181',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('183',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('184',plain,(
    ! [X29: $i] :
      ( ( v1_funct_2 @ X29 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['181','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['179','191'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['192','193','194','195','196'])).

thf('198',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','197'])).

thf('199',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('200',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','198','199'])).

thf('201',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','200'])).

thf('202',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('203',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('204',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('206',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('207',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['205','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['204','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['202','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('218',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('219',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('222',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('224',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','198','199'])).

thf('226',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['224','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','226','227','228','229'])).

thf('231',plain,(
    $false ),
    inference(demod,[status(thm)],['201','230'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0sq0g2uLJB
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.76/18.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.76/18.99  % Solved by: fo/fo7.sh
% 18.76/18.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.76/18.99  % done 12654 iterations in 18.522s
% 18.76/18.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.76/18.99  % SZS output start Refutation
% 18.76/18.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.76/18.99  thf(sk_A_type, type, sk_A: $i).
% 18.76/18.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 18.76/18.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.76/18.99  thf(sk_C_type, type, sk_C: $i).
% 18.76/18.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 18.76/18.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 18.76/18.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.76/18.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 18.76/18.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.76/18.99  thf(sk_B_type, type, sk_B: $i).
% 18.76/18.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.76/18.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 18.76/18.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 18.76/18.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 18.76/18.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.76/18.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 18.76/18.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 18.76/18.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.76/18.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 18.76/18.99  thf(t31_funct_2, conjecture,
% 18.76/18.99    (![A:$i,B:$i,C:$i]:
% 18.76/18.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.76/18.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.76/18.99       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 18.76/18.99         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 18.76/18.99           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 18.76/18.99           ( m1_subset_1 @
% 18.76/18.99             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 18.76/18.99  thf(zf_stmt_0, negated_conjecture,
% 18.76/18.99    (~( ![A:$i,B:$i,C:$i]:
% 18.76/18.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.76/18.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.76/18.99          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 18.76/18.99            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 18.76/18.99              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 18.76/18.99              ( m1_subset_1 @
% 18.76/18.99                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 18.76/18.99    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 18.76/18.99  thf('0', plain,
% 18.76/18.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 18.76/18.99        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 18.76/18.99        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('1', plain,
% 18.76/18.99      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 18.76/18.99         <= (~
% 18.76/18.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 18.76/18.99      inference('split', [status(esa)], ['0'])).
% 18.76/18.99  thf('2', plain,
% 18.76/18.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf(cc1_relset_1, axiom,
% 18.76/18.99    (![A:$i,B:$i,C:$i]:
% 18.76/18.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.76/18.99       ( v1_relat_1 @ C ) ))).
% 18.76/18.99  thf('3', plain,
% 18.76/18.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 18.76/18.99         ((v1_relat_1 @ X9)
% 18.76/18.99          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 18.76/18.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 18.76/18.99  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf(dt_k2_funct_1, axiom,
% 18.76/18.99    (![A:$i]:
% 18.76/18.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.76/18.99       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 18.76/18.99         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 18.76/18.99  thf('5', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('6', plain,
% 18.76/18.99      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 18.76/18.99         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 18.76/18.99      inference('split', [status(esa)], ['0'])).
% 18.76/18.99  thf('7', plain,
% 18.76/18.99      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 18.76/18.99         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['5', '6'])).
% 18.76/18.99  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('9', plain,
% 18.76/18.99      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 18.76/18.99      inference('demod', [status(thm)], ['7', '8'])).
% 18.76/18.99  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['4', '9'])).
% 18.76/18.99  thf('11', plain,
% 18.76/18.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('split', [status(esa)], ['0'])).
% 18.76/18.99  thf(d1_funct_2, axiom,
% 18.76/18.99    (![A:$i,B:$i,C:$i]:
% 18.76/18.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.76/18.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.76/18.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 18.76/18.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 18.76/18.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.76/18.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 18.76/18.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 18.76/18.99  thf(zf_stmt_1, axiom,
% 18.76/18.99    (![B:$i,A:$i]:
% 18.76/18.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.76/18.99       ( zip_tseitin_0 @ B @ A ) ))).
% 18.76/18.99  thf('12', plain,
% 18.76/18.99      (![X21 : $i, X22 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.76/18.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 18.76/18.99  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 18.76/18.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 18.76/18.99  thf('14', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 18.76/18.99      inference('sup+', [status(thm)], ['12', '13'])).
% 18.76/18.99  thf('15', plain,
% 18.76/18.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf(redefinition_k2_relset_1, axiom,
% 18.76/18.99    (![A:$i,B:$i,C:$i]:
% 18.76/18.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.76/18.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 18.76/18.99  thf('16', plain,
% 18.76/18.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 18.76/18.99         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 18.76/18.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 18.76/18.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.76/18.99  thf('17', plain,
% 18.76/18.99      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 18.76/18.99      inference('sup-', [status(thm)], ['15', '16'])).
% 18.76/18.99  thf('18', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('19', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.76/18.99      inference('sup+', [status(thm)], ['17', '18'])).
% 18.76/18.99  thf('20', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('21', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf(t55_funct_1, axiom,
% 18.76/18.99    (![A:$i]:
% 18.76/18.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.76/18.99       ( ( v2_funct_1 @ A ) =>
% 18.76/18.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 18.76/18.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 18.76/18.99  thf('22', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf(t3_funct_2, axiom,
% 18.76/18.99    (![A:$i]:
% 18.76/18.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.76/18.99       ( ( v1_funct_1 @ A ) & 
% 18.76/18.99         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 18.76/18.99         ( m1_subset_1 @
% 18.76/18.99           A @ 
% 18.76/18.99           ( k1_zfmisc_1 @
% 18.76/18.99             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 18.76/18.99  thf('23', plain,
% 18.76/18.99      (![X29 : $i]:
% 18.76/18.99         ((m1_subset_1 @ X29 @ 
% 18.76/18.99           (k1_zfmisc_1 @ 
% 18.76/18.99            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))))
% 18.76/18.99          | ~ (v1_funct_1 @ X29)
% 18.76/18.99          | ~ (v1_relat_1 @ X29))),
% 18.76/18.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 18.76/18.99  thf(cc3_relset_1, axiom,
% 18.76/18.99    (![A:$i,B:$i]:
% 18.76/18.99     ( ( v1_xboole_0 @ A ) =>
% 18.76/18.99       ( ![C:$i]:
% 18.76/18.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.76/18.99           ( v1_xboole_0 @ C ) ) ) ))).
% 18.76/18.99  thf('24', plain,
% 18.76/18.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X12)
% 18.76/18.99          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 18.76/18.99          | (v1_xboole_0 @ X13))),
% 18.76/18.99      inference('cnf', [status(esa)], [cc3_relset_1])).
% 18.76/18.99  thf('25', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | (v1_xboole_0 @ X0)
% 18.76/18.99          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['23', '24'])).
% 18.76/18.99  thf('26', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['22', '25'])).
% 18.76/18.99  thf('27', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['21', '26'])).
% 18.76/18.99  thf('28', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['27'])).
% 18.76/18.99  thf('29', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['20', '28'])).
% 18.76/18.99  thf('30', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['29'])).
% 18.76/18.99  thf('31', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_B)
% 18.76/18.99        | ~ (v1_relat_1 @ sk_C)
% 18.76/18.99        | ~ (v1_funct_1 @ sk_C)
% 18.76/18.99        | (v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 18.76/18.99        | ~ (v2_funct_1 @ sk_C))),
% 18.76/18.99      inference('sup-', [status(thm)], ['19', '30'])).
% 18.76/18.99  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('35', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 18.76/18.99  thf('36', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['14', '35'])).
% 18.76/18.99  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 18.76/18.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 18.76/18.99  thf(t8_boole, axiom,
% 18.76/18.99    (![A:$i,B:$i]:
% 18.76/18.99     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 18.76/18.99  thf('38', plain,
% 18.76/18.99      (![X1 : $i, X2 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 18.76/18.99      inference('cnf', [status(esa)], [t8_boole])).
% 18.76/18.99  thf('39', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('40', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ sk_B @ X0) | ((k1_xboole_0) = (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['36', '39'])).
% 18.76/18.99  thf('41', plain,
% 18.76/18.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 18.76/18.99  thf(zf_stmt_3, axiom,
% 18.76/18.99    (![C:$i,B:$i,A:$i]:
% 18.76/18.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 18.76/18.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 18.76/18.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 18.76/18.99  thf(zf_stmt_5, axiom,
% 18.76/18.99    (![A:$i,B:$i,C:$i]:
% 18.76/18.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.76/18.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 18.76/18.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.76/18.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 18.76/18.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 18.76/18.99  thf('42', plain,
% 18.76/18.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.76/18.99         (~ (zip_tseitin_0 @ X26 @ X27)
% 18.76/18.99          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 18.76/18.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.76/18.99  thf('43', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['41', '42'])).
% 18.76/18.99  thf('44', plain,
% 18.76/18.99      ((((k1_xboole_0) = (k2_funct_1 @ sk_C))
% 18.76/18.99        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['40', '43'])).
% 18.76/18.99  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('46', plain,
% 18.76/18.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.76/18.99         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 18.76/18.99          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 18.76/18.99          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.99  thf('47', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 18.76/18.99        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['45', '46'])).
% 18.76/18.99  thf('48', plain,
% 18.76/18.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf(redefinition_k1_relset_1, axiom,
% 18.76/18.99    (![A:$i,B:$i,C:$i]:
% 18.76/18.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.76/18.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 18.76/18.99  thf('49', plain,
% 18.76/18.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 18.76/18.99         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 18.76/18.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 18.76/18.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.76/18.99  thf('50', plain,
% 18.76/18.99      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 18.76/18.99      inference('sup-', [status(thm)], ['48', '49'])).
% 18.76/18.99  thf('51', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('52', plain,
% 18.76/18.99      ((((k1_xboole_0) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['44', '51'])).
% 18.76/18.99  thf('53', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf('54', plain,
% 18.76/18.99      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ k1_xboole_0))
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99        | ~ (v1_relat_1 @ sk_C)
% 18.76/18.99        | ~ (v1_funct_1 @ sk_C)
% 18.76/18.99        | ~ (v2_funct_1 @ sk_C))),
% 18.76/18.99      inference('sup+', [status(thm)], ['52', '53'])).
% 18.76/18.99  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('58', plain,
% 18.76/18.99      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ k1_xboole_0))
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 18.76/18.99  thf('59', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('60', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf(t65_relat_1, axiom,
% 18.76/18.99    (![A:$i]:
% 18.76/18.99     ( ( v1_relat_1 @ A ) =>
% 18.76/18.99       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 18.76/18.99         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 18.76/18.99  thf('61', plain,
% 18.76/18.99      (![X6 : $i]:
% 18.76/18.99         (((k2_relat_1 @ X6) != (k1_xboole_0))
% 18.76/18.99          | ((k1_relat_1 @ X6) = (k1_xboole_0))
% 18.76/18.99          | ~ (v1_relat_1 @ X6))),
% 18.76/18.99      inference('cnf', [status(esa)], [t65_relat_1])).
% 18.76/18.99  thf('62', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['60', '61'])).
% 18.76/18.99  thf('63', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ((k1_relat_1 @ X0) != (k1_xboole_0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['59', '62'])).
% 18.76/18.99  thf('64', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0))
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['63'])).
% 18.76/18.99  thf('65', plain,
% 18.76/18.99      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99        | ~ (v1_relat_1 @ sk_C)
% 18.76/18.99        | ~ (v1_funct_1 @ sk_C)
% 18.76/18.99        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 18.76/18.99        | ~ (v2_funct_1 @ sk_C))),
% 18.76/18.99      inference('sup-', [status(thm)], ['58', '64'])).
% 18.76/18.99  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('69', plain,
% 18.76/18.99      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0)))),
% 18.76/18.99      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 18.76/18.99  thf('70', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 18.76/18.99      inference('sup+', [status(thm)], ['12', '13'])).
% 18.76/18.99  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.76/18.99      inference('sup+', [status(thm)], ['17', '18'])).
% 18.76/18.99  thf('72', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf('73', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 18.76/18.99  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 18.76/18.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 18.76/18.99  thf(t3_subset, axiom,
% 18.76/18.99    (![A:$i,B:$i]:
% 18.76/18.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 18.76/18.99  thf('75', plain,
% 18.76/18.99      (![X3 : $i, X5 : $i]:
% 18.76/18.99         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 18.76/18.99      inference('cnf', [status(esa)], [t3_subset])).
% 18.76/18.99  thf('76', plain,
% 18.76/18.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['74', '75'])).
% 18.76/18.99  thf('77', plain,
% 18.76/18.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 18.76/18.99         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 18.76/18.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 18.76/18.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.76/18.99  thf('78', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['76', '77'])).
% 18.76/18.99  thf('79', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('80', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 18.76/18.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 18.76/18.99  thf('81', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup+', [status(thm)], ['79', '80'])).
% 18.76/18.99  thf('82', plain,
% 18.76/18.99      (![X3 : $i, X5 : $i]:
% 18.76/18.99         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 18.76/18.99      inference('cnf', [status(esa)], [t3_subset])).
% 18.76/18.99  thf('83', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['81', '82'])).
% 18.76/18.99  thf('84', plain,
% 18.76/18.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 18.76/18.99         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 18.76/18.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 18.76/18.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.76/18.99  thf('85', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X2)
% 18.76/18.99          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['83', '84'])).
% 18.76/18.99  thf('86', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('87', plain,
% 18.76/18.99      (![X6 : $i]:
% 18.76/18.99         (((k1_relat_1 @ X6) != (k1_xboole_0))
% 18.76/18.99          | ((k2_relat_1 @ X6) = (k1_xboole_0))
% 18.76/18.99          | ~ (v1_relat_1 @ X6))),
% 18.76/18.99      inference('cnf', [status(esa)], [t65_relat_1])).
% 18.76/18.99  thf('88', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         (((k1_relat_1 @ X1) != (X0))
% 18.76/18.99          | ~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X1)
% 18.76/18.99          | ((k2_relat_1 @ X1) = (k1_xboole_0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['86', '87'])).
% 18.76/18.99  thf('89', plain,
% 18.76/18.99      (![X1 : $i]:
% 18.76/18.99         (((k2_relat_1 @ X1) = (k1_xboole_0))
% 18.76/18.99          | ~ (v1_relat_1 @ X1)
% 18.76/18.99          | ~ (v1_xboole_0 @ (k1_relat_1 @ X1)))),
% 18.76/18.99      inference('simplify', [status(thm)], ['88'])).
% 18.76/18.99  thf('90', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ (k1_relset_1 @ X2 @ X1 @ X0))
% 18.76/18.99          | ~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['85', '89'])).
% 18.76/18.99  thf('91', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 18.76/18.99        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 18.76/18.99        | ~ (v1_relat_1 @ k1_xboole_0)
% 18.76/18.99        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['78', '90'])).
% 18.76/18.99  thf('92', plain,
% 18.76/18.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['74', '75'])).
% 18.76/18.99  thf('93', plain,
% 18.76/18.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 18.76/18.99         ((v1_relat_1 @ X9)
% 18.76/18.99          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 18.76/18.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 18.76/18.99  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 18.76/18.99      inference('sup-', [status(thm)], ['92', '93'])).
% 18.76/18.99  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 18.76/18.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 18.76/18.99  thf('96', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 18.76/18.99        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 18.76/18.99      inference('demod', [status(thm)], ['91', '94', '95'])).
% 18.76/18.99  thf('97', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 18.76/18.99          | ~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['73', '96'])).
% 18.76/18.99  thf('98', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 18.76/18.99          | ~ (v1_xboole_0 @ (k2_funct_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['72', '97'])).
% 18.76/18.99  thf('99', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_B)
% 18.76/18.99        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 18.76/18.99        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 18.76/18.99        | ~ (v2_funct_1 @ sk_C)
% 18.76/18.99        | ~ (v1_funct_1 @ sk_C)
% 18.76/18.99        | ~ (v1_relat_1 @ sk_C))),
% 18.76/18.99      inference('sup-', [status(thm)], ['71', '98'])).
% 18.76/18.99  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('103', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_B)
% 18.76/18.99        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 18.76/18.99        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 18.76/18.99      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 18.76/18.99  thf('104', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 18.76/18.99  thf('105', plain,
% 18.76/18.99      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B))),
% 18.76/18.99      inference('clc', [status(thm)], ['103', '104'])).
% 18.76/18.99  thf('106', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ sk_B @ X0)
% 18.76/18.99          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['70', '105'])).
% 18.76/18.99  thf('107', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['41', '42'])).
% 18.76/18.99  thf('108', plain,
% 18.76/18.99      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 18.76/18.99        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['106', '107'])).
% 18.76/18.99  thf('109', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('110', plain,
% 18.76/18.99      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['108', '109'])).
% 18.76/18.99  thf('111', plain,
% 18.76/18.99      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('clc', [status(thm)], ['69', '110'])).
% 18.76/18.99  thf('112', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('113', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 18.76/18.99      inference('sup+', [status(thm)], ['12', '13'])).
% 18.76/18.99  thf('114', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('115', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('116', plain,
% 18.76/18.99      (![X21 : $i, X22 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.76/18.99  thf('117', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 18.76/18.99      inference('simplify', [status(thm)], ['116'])).
% 18.76/18.99  thf('118', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup+', [status(thm)], ['115', '117'])).
% 18.76/18.99  thf('119', plain,
% 18.76/18.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['74', '75'])).
% 18.76/18.99  thf('120', plain,
% 18.76/18.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.76/18.99         (~ (zip_tseitin_0 @ X26 @ X27)
% 18.76/18.99          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 18.76/18.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.76/18.99  thf('121', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 18.76/18.99      inference('sup-', [status(thm)], ['119', '120'])).
% 18.76/18.99  thf('122', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X0) | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['118', '121'])).
% 18.76/18.99  thf('123', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.99         ((zip_tseitin_1 @ X0 @ X2 @ X1)
% 18.76/18.99          | ~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ~ (v1_xboole_0 @ X1))),
% 18.76/18.99      inference('sup+', [status(thm)], ['114', '122'])).
% 18.76/18.99  thf('124', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('125', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_A)
% 18.76/18.99        | ~ (v1_xboole_0 @ sk_C)
% 18.76/18.99        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['123', '124'])).
% 18.76/18.99  thf('126', plain,
% 18.76/18.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('127', plain,
% 18.76/18.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X12)
% 18.76/18.99          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 18.76/18.99          | (v1_xboole_0 @ X13))),
% 18.76/18.99      inference('cnf', [status(esa)], [cc3_relset_1])).
% 18.76/18.99  thf('128', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['126', '127'])).
% 18.76/18.99  thf('129', plain,
% 18.76/18.99      ((((sk_A) = (k1_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ sk_A))),
% 18.76/18.99      inference('clc', [status(thm)], ['125', '128'])).
% 18.76/18.99  thf('130', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['113', '129'])).
% 18.76/18.99  thf('131', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 18.76/18.99      inference('sup-', [status(thm)], ['119', '120'])).
% 18.76/18.99  thf('132', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99          | (zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['130', '131'])).
% 18.76/18.99  thf('133', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X2)
% 18.76/18.99          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['83', '84'])).
% 18.76/18.99  thf('134', plain,
% 18.76/18.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.76/18.99         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 18.76/18.99          | (v1_funct_2 @ X25 @ X23 @ X24)
% 18.76/18.99          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.99  thf('135', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.99         (((X2) != (k1_relat_1 @ X0))
% 18.76/18.99          | ~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ~ (zip_tseitin_1 @ X0 @ X1 @ X2)
% 18.76/18.99          | (v1_funct_2 @ X0 @ X2 @ X1))),
% 18.76/18.99      inference('sup-', [status(thm)], ['133', '134'])).
% 18.76/18.99  thf('136', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 18.76/18.99          | ~ (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 18.76/18.99          | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['135'])).
% 18.76/18.99  thf('137', plain,
% 18.76/18.99      ((((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99        | ~ (v1_xboole_0 @ k1_xboole_0)
% 18.76/18.99        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['132', '136'])).
% 18.76/18.99  thf('138', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 18.76/18.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 18.76/18.99  thf('139', plain,
% 18.76/18.99      ((((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A))),
% 18.76/18.99      inference('demod', [status(thm)], ['137', '138'])).
% 18.76/18.99  thf('140', plain,
% 18.76/18.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 18.76/18.99      inference('sup-', [status(thm)], ['37', '38'])).
% 18.76/18.99  thf('141', plain,
% 18.76/18.99      (![X21 : $i, X22 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.76/18.99  thf('142', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.99         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 18.76/18.99      inference('sup+', [status(thm)], ['140', '141'])).
% 18.76/18.99  thf('143', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['41', '42'])).
% 18.76/18.99  thf('144', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ((sk_B) = (X0))
% 18.76/18.99          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['142', '143'])).
% 18.76/18.99  thf('145', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('146', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (((sk_B) = (X0))
% 18.76/18.99          | ~ (v1_xboole_0 @ X0)
% 18.76/18.99          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['144', '145'])).
% 18.76/18.99  thf('147', plain,
% 18.76/18.99      ((((k1_xboole_0) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['44', '51'])).
% 18.76/18.99  thf('148', plain,
% 18.76/18.99      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('split', [status(esa)], ['0'])).
% 18.76/18.99  thf('149', plain,
% 18.76/18.99      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 18.76/18.99         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['147', '148'])).
% 18.76/18.99  thf('150', plain,
% 18.76/18.99      ((![X0 : $i]:
% 18.76/18.99          (~ (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A)
% 18.76/18.99           | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99           | ~ (v1_xboole_0 @ X0)
% 18.76/18.99           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['146', '149'])).
% 18.76/18.99  thf('151', plain,
% 18.76/18.99      ((![X0 : $i]:
% 18.76/18.99          (~ (v1_xboole_0 @ X0)
% 18.76/18.99           | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99           | ~ (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A)))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('simplify', [status(thm)], ['150'])).
% 18.76/18.99  thf('152', plain,
% 18.76/18.99      (((((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99         | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99         | ~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['139', '151'])).
% 18.76/18.99  thf('153', plain,
% 18.76/18.99      (((~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 18.76/18.99         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('simplify', [status(thm)], ['152'])).
% 18.76/18.99  thf('154', plain,
% 18.76/18.99      ((![X0 : $i]:
% 18.76/18.99          (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 18.76/18.99           | ~ (v1_xboole_0 @ X0)
% 18.76/18.99           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['112', '153'])).
% 18.76/18.99  thf('155', plain,
% 18.76/18.99      (((~ (v1_xboole_0 @ k1_xboole_0)
% 18.76/18.99         | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99         | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99         | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['111', '154'])).
% 18.76/18.99  thf('156', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 18.76/18.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 18.76/18.99  thf('157', plain,
% 18.76/18.99      (((((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99         | ((sk_A) = (k1_relat_1 @ sk_C))
% 18.76/18.99         | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('demod', [status(thm)], ['155', '156'])).
% 18.76/18.99  thf('158', plain,
% 18.76/18.99      (((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('simplify', [status(thm)], ['157'])).
% 18.76/18.99  thf('159', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 18.76/18.99      inference('sup+', [status(thm)], ['12', '13'])).
% 18.76/18.99  thf('160', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['41', '42'])).
% 18.76/18.99  thf('161', plain,
% 18.76/18.99      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['159', '160'])).
% 18.76/18.99  thf('162', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('163', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['161', '162'])).
% 18.76/18.99  thf('164', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['14', '35'])).
% 18.76/18.99  thf('165', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.76/18.99      inference('sup+', [status(thm)], ['17', '18'])).
% 18.76/18.99  thf('166', plain,
% 18.76/18.99      (![X29 : $i]:
% 18.76/18.99         ((m1_subset_1 @ X29 @ 
% 18.76/18.99           (k1_zfmisc_1 @ 
% 18.76/18.99            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))))
% 18.76/18.99          | ~ (v1_funct_1 @ X29)
% 18.76/18.99          | ~ (v1_relat_1 @ X29))),
% 18.76/18.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 18.76/18.99  thf('167', plain,
% 18.76/18.99      (((m1_subset_1 @ sk_C @ 
% 18.76/18.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 18.76/18.99        | ~ (v1_relat_1 @ sk_C)
% 18.76/18.99        | ~ (v1_funct_1 @ sk_C))),
% 18.76/18.99      inference('sup+', [status(thm)], ['165', '166'])).
% 18.76/18.99  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('170', plain,
% 18.76/18.99      ((m1_subset_1 @ sk_C @ 
% 18.76/18.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 18.76/18.99      inference('demod', [status(thm)], ['167', '168', '169'])).
% 18.76/18.99  thf('171', plain,
% 18.76/18.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.76/18.99         (~ (zip_tseitin_0 @ X26 @ X27)
% 18.76/18.99          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 18.76/18.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.76/18.99  thf('172', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))
% 18.76/18.99        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['170', '171'])).
% 18.76/18.99  thf('173', plain,
% 18.76/18.99      (((v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 18.76/18.99        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['164', '172'])).
% 18.76/18.99  thf('174', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 18.76/18.99        | (v1_xboole_0 @ sk_B)
% 18.76/18.99        | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('sup+', [status(thm)], ['163', '173'])).
% 18.76/18.99  thf('175', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 18.76/18.99  thf('176', plain,
% 18.76/18.99      (((v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 18.76/18.99        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 18.76/18.99      inference('clc', [status(thm)], ['174', '175'])).
% 18.76/18.99  thf('177', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('178', plain,
% 18.76/18.99      (((v1_xboole_0 @ (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['176', '177'])).
% 18.76/18.99  thf('179', plain,
% 18.76/18.99      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('clc', [status(thm)], ['158', '178'])).
% 18.76/18.99  thf('180', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf('181', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('182', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('183', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf('184', plain,
% 18.76/18.99      (![X29 : $i]:
% 18.76/18.99         ((v1_funct_2 @ X29 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))
% 18.76/18.99          | ~ (v1_funct_1 @ X29)
% 18.76/18.99          | ~ (v1_relat_1 @ X29))),
% 18.76/18.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 18.76/18.99  thf('185', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 18.76/18.99      inference('sup+', [status(thm)], ['183', '184'])).
% 18.76/18.99  thf('186', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['182', '185'])).
% 18.76/18.99  thf('187', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['186'])).
% 18.76/18.99  thf('188', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['181', '187'])).
% 18.76/18.99  thf('189', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['188'])).
% 18.76/18.99  thf('190', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99           (k1_relat_1 @ X0))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0))),
% 18.76/18.99      inference('sup+', [status(thm)], ['180', '189'])).
% 18.76/18.99  thf('191', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 18.76/18.99             (k1_relat_1 @ X0)))),
% 18.76/18.99      inference('simplify', [status(thm)], ['190'])).
% 18.76/18.99  thf('192', plain,
% 18.76/18.99      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 18.76/18.99         | ~ (v1_relat_1 @ sk_C)
% 18.76/18.99         | ~ (v1_funct_1 @ sk_C)
% 18.76/18.99         | ~ (v2_funct_1 @ sk_C)))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('sup+', [status(thm)], ['179', '191'])).
% 18.76/18.99  thf('193', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.76/18.99      inference('sup+', [status(thm)], ['17', '18'])).
% 18.76/18.99  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('197', plain,
% 18.76/18.99      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 18.76/18.99         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 18.76/18.99      inference('demod', [status(thm)], ['192', '193', '194', '195', '196'])).
% 18.76/18.99  thf('198', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 18.76/18.99      inference('demod', [status(thm)], ['11', '197'])).
% 18.76/18.99  thf('199', plain,
% 18.76/18.99      (~
% 18.76/18.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 18.76/18.99       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 18.76/18.99       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('split', [status(esa)], ['0'])).
% 18.76/18.99  thf('200', plain,
% 18.76/18.99      (~
% 18.76/18.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 18.76/18.99      inference('sat_resolution*', [status(thm)], ['10', '198', '199'])).
% 18.76/18.99  thf('201', plain,
% 18.76/18.99      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.76/18.99      inference('simpl_trail', [status(thm)], ['1', '200'])).
% 18.76/18.99  thf('202', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 18.76/18.99      inference('sup+', [status(thm)], ['17', '18'])).
% 18.76/18.99  thf('203', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf('204', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('205', plain,
% 18.76/18.99      (![X7 : $i]:
% 18.76/18.99         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 18.76/18.99          | ~ (v1_funct_1 @ X7)
% 18.76/18.99          | ~ (v1_relat_1 @ X7))),
% 18.76/18.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 18.76/18.99  thf('206', plain,
% 18.76/18.99      (![X8 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X8)
% 18.76/18.99          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 18.76/18.99          | ~ (v1_funct_1 @ X8)
% 18.76/18.99          | ~ (v1_relat_1 @ X8))),
% 18.76/18.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 18.76/18.99  thf('207', plain,
% 18.76/18.99      (![X29 : $i]:
% 18.76/18.99         ((m1_subset_1 @ X29 @ 
% 18.76/18.99           (k1_zfmisc_1 @ 
% 18.76/18.99            (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29))))
% 18.76/18.99          | ~ (v1_funct_1 @ X29)
% 18.76/18.99          | ~ (v1_relat_1 @ X29))),
% 18.76/18.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 18.76/18.99  thf('208', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99           (k1_zfmisc_1 @ 
% 18.76/18.99            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 18.76/18.99      inference('sup+', [status(thm)], ['206', '207'])).
% 18.76/18.99  thf('209', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99             (k1_zfmisc_1 @ 
% 18.76/18.99              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 18.76/18.99               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['205', '208'])).
% 18.76/18.99  thf('210', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99           (k1_zfmisc_1 @ 
% 18.76/18.99            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['209'])).
% 18.76/18.99  thf('211', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99             (k1_zfmisc_1 @ 
% 18.76/18.99              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 18.76/18.99               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['204', '210'])).
% 18.76/18.99  thf('212', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99           (k1_zfmisc_1 @ 
% 18.76/18.99            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0))),
% 18.76/18.99      inference('simplify', [status(thm)], ['211'])).
% 18.76/18.99  thf('213', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v2_funct_1 @ X0))),
% 18.76/18.99      inference('sup+', [status(thm)], ['203', '212'])).
% 18.76/18.99  thf('214', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         (~ (v2_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_funct_1 @ X0)
% 18.76/18.99          | ~ (v1_relat_1 @ X0)
% 18.76/18.99          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 18.76/18.99             (k1_zfmisc_1 @ 
% 18.76/18.99              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 18.76/18.99      inference('simplify', [status(thm)], ['213'])).
% 18.76/18.99  thf('215', plain,
% 18.76/18.99      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 18.76/18.99        | ~ (v1_relat_1 @ sk_C)
% 18.76/18.99        | ~ (v1_funct_1 @ sk_C)
% 18.76/18.99        | ~ (v2_funct_1 @ sk_C))),
% 18.76/18.99      inference('sup+', [status(thm)], ['202', '214'])).
% 18.76/18.99  thf('216', plain,
% 18.76/18.99      (![X0 : $i]:
% 18.76/18.99         ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['14', '35'])).
% 18.76/18.99  thf('217', plain,
% 18.76/18.99      (![X0 : $i, X1 : $i]:
% 18.76/18.99         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 18.76/18.99      inference('sup-', [status(thm)], ['81', '82'])).
% 18.76/18.99  thf('218', plain,
% 18.76/18.99      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 18.76/18.99         <= (~
% 18.76/18.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 18.76/18.99      inference('split', [status(esa)], ['0'])).
% 18.76/18.99  thf('219', plain,
% 18.76/18.99      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 18.76/18.99         <= (~
% 18.76/18.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['217', '218'])).
% 18.76/18.99  thf('220', plain,
% 18.76/18.99      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 18.76/18.99         <= (~
% 18.76/18.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['216', '219'])).
% 18.76/18.99  thf('221', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.76/18.99      inference('sup-', [status(thm)], ['41', '42'])).
% 18.76/18.99  thf('222', plain,
% 18.76/18.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 18.76/18.99         <= (~
% 18.76/18.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['220', '221'])).
% 18.76/18.99  thf('223', plain,
% 18.76/18.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 18.76/18.99      inference('demod', [status(thm)], ['47', '50'])).
% 18.76/18.99  thf('224', plain,
% 18.76/18.99      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 18.76/18.99         <= (~
% 18.76/18.99             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 18.76/18.99      inference('sup-', [status(thm)], ['222', '223'])).
% 18.76/18.99  thf('225', plain,
% 18.76/18.99      (~
% 18.76/18.99       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 18.76/18.99      inference('sat_resolution*', [status(thm)], ['10', '198', '199'])).
% 18.76/18.99  thf('226', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 18.76/18.99      inference('simpl_trail', [status(thm)], ['224', '225'])).
% 18.76/18.99  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 18.76/18.99      inference('sup-', [status(thm)], ['2', '3'])).
% 18.76/18.99  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 18.76/18.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.99  thf('230', plain,
% 18.76/18.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 18.76/18.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.76/18.99      inference('demod', [status(thm)], ['215', '226', '227', '228', '229'])).
% 18.76/18.99  thf('231', plain, ($false), inference('demod', [status(thm)], ['201', '230'])).
% 18.76/18.99  
% 18.76/18.99  % SZS output end Refutation
% 18.76/18.99  
% 18.84/18.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
