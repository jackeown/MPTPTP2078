%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BKiKKY7qog

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 585 expanded)
%              Number of leaves         :   36 ( 184 expanded)
%              Depth                    :   17
%              Number of atoms          :  919 (9455 expanded)
%              Number of equality atoms :   72 ( 365 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k3_relset_1 @ X17 @ X18 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','19','20'])).

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
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['38'])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('50',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['38'])).

thf('55',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','53','54'])).

thf('56',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['41','55'])).

thf('57',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','56'])).

thf('58',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('60',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','57'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('77',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('80',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('87',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['62','84','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BKiKKY7qog
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 202 iterations in 0.148s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.38/0.60  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(t31_funct_2, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.38/0.60         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.38/0.60           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.38/0.60           ( m1_subset_1 @
% 0.38/0.60             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.38/0.60            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.38/0.60              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.38/0.60              ( m1_subset_1 @
% 0.38/0.60                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_k3_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @
% 0.38/0.60         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.38/0.60         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k3_relset_1 @ X7 @ X8 @ X9) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.38/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k3_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.60         (((k3_relset_1 @ X17 @ X18 @ X16) = (k4_relat_1 @ X16))
% 0.38/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.38/0.60  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '5'])).
% 0.38/0.60  thf(d1_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_2, axiom,
% 0.38/0.60    (![C:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_4, axiom,
% 0.38/0.60    (![B:$i,A:$i]:
% 0.38/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.60  thf(zf_stmt_5, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.38/0.60          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.38/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.38/0.60        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.60         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.38/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.38/0.60         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( v1_relat_1 @ C ) ))).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.60         ((v1_relat_1 @ X4)
% 0.38/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.60  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf(d9_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X1)
% 0.38/0.60          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.38/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.60  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('20', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('21', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.60  thf(t55_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v2_funct_1 @ A ) =>
% 0.38/0.60         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.60           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X3 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X3)
% 0.38/0.60          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.38/0.60          | ~ (v1_funct_1 @ X3)
% 0.38/0.60          | ~ (v1_relat_1 @ X3))),
% 0.38/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.60  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('26', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.60      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.38/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('32', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.60      inference('demod', [status(thm)], ['27', '32'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '12', '13', '33'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 0.38/0.60          | (v1_funct_2 @ X23 @ X21 @ X22)
% 0.38/0.60          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((((sk_B) != (sk_B))
% 0.38/0.60        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.38/0.60        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.38/0.60        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.38/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.38/0.60        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.38/0.60         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.38/0.60      inference('split', [status(esa)], ['38'])).
% 0.38/0.60  thf('40', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.38/0.60         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf(dt_k2_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.60         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (![X2 : $i]:
% 0.38/0.60         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.38/0.60          | ~ (v1_funct_1 @ X2)
% 0.38/0.60          | ~ (v1_relat_1 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.60         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.60      inference('split', [status(esa)], ['38'])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.38/0.60         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf('48', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['42', '47'])).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '5'])).
% 0.38/0.60  thf('50', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.38/0.60      inference('split', [status(esa)], ['38'])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['49', '52'])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.38/0.60       ~
% 0.38/0.60       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.38/0.60       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['38'])).
% 0.38/0.60  thf('55', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['48', '53', '54'])).
% 0.38/0.60  thf('56', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['41', '55'])).
% 0.38/0.60  thf('57', plain, (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 0.38/0.60      inference('clc', [status(thm)], ['37', '56'])).
% 0.38/0.60  thf('58', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.38/0.60      inference('clc', [status(thm)], ['8', '57'])).
% 0.38/0.60  thf('59', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf('60', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.38/0.60      inference('clc', [status(thm)], ['8', '57'])).
% 0.38/0.60  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.60  thf('62', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['58', '61'])).
% 0.38/0.60  thf('63', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf('64', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('65', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.38/0.60          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.38/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.60  thf('66', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['63', '66'])).
% 0.38/0.60  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('69', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.38/0.60          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.38/0.60          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.38/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.60  thf('71', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('72', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.60         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.38/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf('74', plain,
% 0.38/0.60      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.38/0.60      inference('demod', [status(thm)], ['70', '73'])).
% 0.38/0.60  thf('75', plain,
% 0.38/0.60      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['67', '74'])).
% 0.38/0.60  thf(t65_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.60         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf('76', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.38/0.60          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.38/0.60  thf('77', plain,
% 0.38/0.60      ((((sk_A) != (k1_xboole_0))
% 0.38/0.60        | ((sk_B) = (k1_xboole_0))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.60  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf('79', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('80', plain,
% 0.38/0.60      ((((sk_A) != (k1_xboole_0))
% 0.38/0.60        | ((sk_B) = (k1_xboole_0))
% 0.38/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.38/0.60  thf('81', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) != (k1_xboole_0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['80'])).
% 0.38/0.60  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.60  thf('83', plain,
% 0.38/0.60      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('84', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['83'])).
% 0.38/0.60  thf('85', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf('86', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.60  thf('87', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 0.38/0.60      inference('simplify', [status(thm)], ['86'])).
% 0.38/0.60  thf('88', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.38/0.60      inference('sup+', [status(thm)], ['85', '87'])).
% 0.38/0.60  thf('89', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['88'])).
% 0.38/0.60  thf('90', plain, ($false),
% 0.38/0.60      inference('demod', [status(thm)], ['62', '84', '89'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
