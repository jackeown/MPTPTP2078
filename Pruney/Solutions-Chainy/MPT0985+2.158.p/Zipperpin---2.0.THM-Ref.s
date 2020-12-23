%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OGZj8lCjXF

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:49 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  163 (1323 expanded)
%              Number of leaves         :   37 ( 397 expanded)
%              Depth                    :   22
%              Number of atoms          : 1169 (20228 expanded)
%              Number of equality atoms :  109 ( 826 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k3_relset_1 @ X18 @ X19 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','22'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('31',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('36',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['29','34','35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['23','36'])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['10','37'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('41',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

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

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['10','37'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('54',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_B )
    | ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('71',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('74',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('80',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('87',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('93',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['92','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('101',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('105',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','106'])).

thf('108',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','78','79','108'])).

thf('110',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('113',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('115',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('117',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('119',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('120',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['118','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['121'])).

thf('123',plain,(
    zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['117','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['110','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OGZj8lCjXF
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.72  % Solved by: fo/fo7.sh
% 0.45/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.72  % done 221 iterations in 0.221s
% 0.45/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.72  % SZS output start Refutation
% 0.45/0.72  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.45/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.45/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.72  thf(t31_funct_2, conjecture,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.72       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.72         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.72           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.72           ( m1_subset_1 @
% 0.45/0.72             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.72          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.72            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.72              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.72              ( m1_subset_1 @
% 0.45/0.72                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.45/0.72    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.45/0.72  thf('0', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(dt_k3_relset_1, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.72       ( m1_subset_1 @
% 0.45/0.72         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.45/0.72         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.45/0.72  thf('1', plain,
% 0.45/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.72         ((m1_subset_1 @ (k3_relset_1 @ X8 @ X9 @ X10) @ 
% 0.45/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.45/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.45/0.72  thf('2', plain,
% 0.45/0.72      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.72  thf('3', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(redefinition_k3_relset_1, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.72       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.45/0.72  thf('4', plain,
% 0.45/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.72         (((k3_relset_1 @ X18 @ X19 @ X17) = (k4_relat_1 @ X17))
% 0.45/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.72      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.45/0.72  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.72  thf('6', plain,
% 0.45/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.72  thf('7', plain,
% 0.45/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.72         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.45/0.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.72  thf('8', plain,
% 0.45/0.72      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))
% 0.45/0.72         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.72  thf(d1_funct_2, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_1, axiom,
% 0.45/0.72    (![C:$i,B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.72  thf('9', plain,
% 0.45/0.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.72         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.45/0.72          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.45/0.72          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.72  thf('10', plain,
% 0.45/0.72      ((((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.45/0.72        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.45/0.72        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.72  thf('11', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.72        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('12', plain,
% 0.45/0.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.45/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.72      inference('split', [status(esa)], ['11'])).
% 0.45/0.72  thf('13', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(cc2_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ![B:$i]:
% 0.45/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.72  thf('14', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.72          | (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X1))),
% 0.45/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.72  thf('15', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.72  thf(fc6_relat_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.72  thf('16', plain,
% 0.45/0.72      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.72  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf(d9_funct_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.45/0.72  thf('18', plain,
% 0.45/0.72      (![X6 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X6)
% 0.45/0.72          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.45/0.72          | ~ (v1_funct_1 @ X6)
% 0.45/0.72          | ~ (v1_relat_1 @ X6))),
% 0.45/0.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.45/0.72  thf('19', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.72  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('21', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('22', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.72  thf('23', plain,
% 0.45/0.72      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.45/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['12', '22'])).
% 0.45/0.72  thf(dt_k2_funct_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.72  thf('24', plain,
% 0.45/0.72      (![X7 : $i]:
% 0.45/0.72         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.45/0.72          | ~ (v1_funct_1 @ X7)
% 0.45/0.72          | ~ (v1_relat_1 @ X7))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('25', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.72      inference('split', [status(esa)], ['11'])).
% 0.45/0.72  thf('26', plain,
% 0.45/0.72      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.45/0.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.72  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('29', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.45/0.72  thf('30', plain,
% 0.45/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.72  thf('31', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.72  thf('32', plain,
% 0.45/0.72      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.45/0.72         <= (~
% 0.45/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.45/0.72      inference('split', [status(esa)], ['11'])).
% 0.45/0.72  thf('33', plain,
% 0.45/0.72      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.45/0.72         <= (~
% 0.45/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.72  thf('34', plain,
% 0.45/0.72      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['30', '33'])).
% 0.45/0.72  thf('35', plain,
% 0.45/0.72      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.45/0.72       ~
% 0.45/0.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.45/0.72       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('split', [status(esa)], ['11'])).
% 0.45/0.72  thf('36', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.45/0.72      inference('sat_resolution*', [status(thm)], ['29', '34', '35'])).
% 0.45/0.72  thf('37', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.45/0.72      inference('simpl_trail', [status(thm)], ['23', '36'])).
% 0.45/0.72  thf('38', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.45/0.72        | ((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.45/0.72      inference('clc', [status(thm)], ['10', '37'])).
% 0.45/0.72  thf(t37_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.45/0.72         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.45/0.72  thf('39', plain,
% 0.45/0.72      (![X4 : $i]:
% 0.45/0.72         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.45/0.72          | ~ (v1_relat_1 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.72  thf(zf_stmt_2, axiom,
% 0.45/0.72    (![B:$i,A:$i]:
% 0.45/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.72  thf('40', plain,
% 0.45/0.72      (![X20 : $i, X21 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.72  thf('41', plain,
% 0.45/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_5, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.72  thf('42', plain,
% 0.45/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.72         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.45/0.72          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.45/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.72  thf('43', plain,
% 0.45/0.72      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.45/0.72        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.45/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.72  thf('44', plain,
% 0.45/0.72      ((((sk_A) = (k1_xboole_0))
% 0.45/0.72        | (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.45/0.72      inference('sup-', [status(thm)], ['40', '43'])).
% 0.45/0.72  thf('45', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.45/0.72        | ((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.45/0.72      inference('clc', [status(thm)], ['10', '37'])).
% 0.45/0.72  thf('46', plain,
% 0.45/0.72      ((((sk_A) = (k1_xboole_0))
% 0.45/0.72        | ((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.72  thf('47', plain,
% 0.45/0.72      ((((sk_B) != (k2_relat_1 @ sk_C))
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['39', '46'])).
% 0.45/0.72  thf('48', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.72  thf('49', plain,
% 0.45/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.72         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.45/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.72  thf('50', plain,
% 0.45/0.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.72  thf('51', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('52', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['50', '51'])).
% 0.45/0.72  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf('54', plain, ((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['47', '52', '53'])).
% 0.45/0.72  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['54'])).
% 0.45/0.72  thf('56', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_B)
% 0.45/0.72        | ((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.45/0.72      inference('demod', [status(thm)], ['38', '55'])).
% 0.45/0.72  thf('57', plain,
% 0.45/0.72      (![X20 : $i, X21 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.72  thf('58', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('59', plain,
% 0.45/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.72         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.45/0.72          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.45/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.72  thf('60', plain,
% 0.45/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.72  thf('61', plain,
% 0.45/0.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['57', '60'])).
% 0.45/0.72  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('63', plain,
% 0.45/0.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.72         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.45/0.72          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.45/0.72          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.72  thf('64', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.45/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.72  thf('65', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('66', plain,
% 0.45/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.72         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.45/0.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.72  thf('67', plain,
% 0.45/0.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.72  thf('68', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['64', '67'])).
% 0.45/0.72  thf('69', plain,
% 0.45/0.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['61', '68'])).
% 0.45/0.72  thf(t65_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.72         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.72  thf('70', plain,
% 0.45/0.72      (![X5 : $i]:
% 0.45/0.72         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 0.45/0.72          | ((k2_relat_1 @ X5) = (k1_xboole_0))
% 0.45/0.72          | ~ (v1_relat_1 @ X5))),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.45/0.72  thf('71', plain,
% 0.45/0.72      ((((sk_A) != (k1_xboole_0))
% 0.45/0.72        | ((sk_B) = (k1_xboole_0))
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.72  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf('73', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['50', '51'])).
% 0.45/0.72  thf('74', plain,
% 0.45/0.72      ((((sk_A) != (k1_xboole_0))
% 0.45/0.72        | ((sk_B) = (k1_xboole_0))
% 0.45/0.72        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.45/0.72  thf('75', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) != (k1_xboole_0)))),
% 0.45/0.72      inference('simplify', [status(thm)], ['74'])).
% 0.45/0.72  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['54'])).
% 0.45/0.72  thf('77', plain,
% 0.45/0.72      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.72  thf('78', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.72  thf('79', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.72  thf('80', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.72  thf('81', plain,
% 0.45/0.72      (![X7 : $i]:
% 0.45/0.72         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.45/0.72          | ~ (v1_funct_1 @ X7)
% 0.45/0.72          | ~ (v1_relat_1 @ X7))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('82', plain,
% 0.45/0.72      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup+', [status(thm)], ['80', '81'])).
% 0.45/0.72  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('85', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.45/0.72  thf('86', plain,
% 0.45/0.72      (![X4 : $i]:
% 0.45/0.72         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.45/0.72          | ~ (v1_relat_1 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.72  thf('87', plain,
% 0.45/0.72      (![X5 : $i]:
% 0.45/0.72         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.45/0.72          | ((k1_relat_1 @ X5) = (k1_xboole_0))
% 0.45/0.72          | ~ (v1_relat_1 @ X5))),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.45/0.72  thf('88', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.45/0.72          | ((k1_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.72  thf('89', plain,
% 0.45/0.72      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0))
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['85', '88'])).
% 0.45/0.72  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf('91', plain,
% 0.45/0.72      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0))
% 0.45/0.72        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.72  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['50', '51'])).
% 0.45/0.72  thf('93', plain,
% 0.45/0.72      (![X20 : $i, X21 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.72  thf('94', plain,
% 0.45/0.72      (![X5 : $i]:
% 0.45/0.72         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.45/0.72          | ((k1_relat_1 @ X5) = (k1_xboole_0))
% 0.45/0.72          | ~ (v1_relat_1 @ X5))),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.45/0.72  thf('95', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.72         (((k2_relat_1 @ X1) != (X0))
% 0.45/0.72          | (zip_tseitin_0 @ X0 @ X2)
% 0.45/0.72          | ~ (v1_relat_1 @ X1)
% 0.45/0.72          | ((k1_relat_1 @ X1) = (k1_xboole_0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['93', '94'])).
% 0.45/0.72  thf('96', plain,
% 0.45/0.72      (![X1 : $i, X2 : $i]:
% 0.45/0.72         (((k1_relat_1 @ X1) = (k1_xboole_0))
% 0.45/0.72          | ~ (v1_relat_1 @ X1)
% 0.45/0.72          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 0.45/0.72      inference('simplify', [status(thm)], ['95'])).
% 0.45/0.72  thf('97', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ sk_B @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72          | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.72      inference('sup+', [status(thm)], ['92', '96'])).
% 0.45/0.72  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.72  thf('99', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ sk_B @ X0) | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['97', '98'])).
% 0.45/0.72  thf('100', plain,
% 0.45/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.72  thf('101', plain,
% 0.45/0.72      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.45/0.72        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['99', '100'])).
% 0.45/0.72  thf('102', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['64', '67'])).
% 0.45/0.72  thf('103', plain,
% 0.45/0.72      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['101', '102'])).
% 0.45/0.72  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['54'])).
% 0.45/0.72  thf('105', plain,
% 0.45/0.72      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.45/0.72        | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['103', '104'])).
% 0.45/0.72  thf('106', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['105'])).
% 0.45/0.72  thf('107', plain,
% 0.45/0.72      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0))
% 0.45/0.72        | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['91', '106'])).
% 0.45/0.72  thf('108', plain, (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['107'])).
% 0.45/0.72  thf('109', plain,
% 0.45/0.72      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.72        | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['56', '78', '79', '108'])).
% 0.45/0.72  thf('110', plain,
% 0.45/0.72      (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.72      inference('simplify', [status(thm)], ['109'])).
% 0.45/0.72  thf('111', plain,
% 0.45/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.72  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['54'])).
% 0.45/0.72  thf('113', plain,
% 0.45/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['111', '112'])).
% 0.45/0.72  thf('114', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.72  thf('115', plain,
% 0.45/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.45/0.72      inference('demod', [status(thm)], ['113', '114'])).
% 0.45/0.72  thf('116', plain,
% 0.45/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.72         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.45/0.72          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.45/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.72  thf('117', plain,
% 0.45/0.72      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.72        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['115', '116'])).
% 0.45/0.72  thf('118', plain,
% 0.45/0.72      (![X20 : $i, X21 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.72  thf('119', plain,
% 0.45/0.72      (![X20 : $i, X21 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.72  thf('120', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.45/0.72      inference('simplify', [status(thm)], ['119'])).
% 0.45/0.72  thf('121', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.72         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.72      inference('sup+', [status(thm)], ['118', '120'])).
% 0.45/0.72  thf('122', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.45/0.72      inference('eq_fact', [status(thm)], ['121'])).
% 0.45/0.72  thf('123', plain,
% 0.45/0.72      ((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.72      inference('demod', [status(thm)], ['117', '122'])).
% 0.45/0.72  thf('124', plain, ($false), inference('demod', [status(thm)], ['110', '123'])).
% 0.45/0.72  
% 0.45/0.72  % SZS output end Refutation
% 0.45/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
