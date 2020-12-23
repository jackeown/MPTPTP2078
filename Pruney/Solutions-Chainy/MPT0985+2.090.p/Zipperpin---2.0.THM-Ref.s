%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0uGPj1JbDh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:39 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 436 expanded)
%              Number of leaves         :   41 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          :  814 (6876 expanded)
%              Number of equality atoms :   55 ( 250 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X20 @ ( k3_relset_1 @ X20 @ X21 @ X22 ) )
        = ( k2_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ X3 )
        = ( k4_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('37',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['35','40','41'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','42'])).

thf('44',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','43'])).

thf('45',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','44'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1
        = ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v4_relat_1 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('62',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('64',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['54','67'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('70',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('73',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['49','70','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0uGPj1JbDh
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 236 iterations in 0.302s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.52/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.76  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.52/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.52/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.76  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.52/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.76  thf(t31_funct_2, conjecture,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.76       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.52/0.76         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.52/0.76           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.52/0.76           ( m1_subset_1 @
% 0.52/0.76             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.76          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.52/0.76            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.52/0.76              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.52/0.76              ( m1_subset_1 @
% 0.52/0.76                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.52/0.76  thf('0', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(dt_k3_relset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( m1_subset_1 @
% 0.52/0.76         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.52/0.76         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k3_relset_1 @ X11 @ X12 @ X13) @ 
% 0.52/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.52/0.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.52/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(redefinition_k3_relset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.76         (((k3_relset_1 @ X18 @ X19 @ X17) = (k4_relat_1 @ X17))
% 0.52/0.76          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.52/0.76      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.52/0.76  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.52/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.76      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.76  thf(d1_funct_2, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.76  thf(zf_stmt_2, axiom,
% 0.52/0.76    (![C:$i,B:$i,A:$i]:
% 0.52/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.76  thf(zf_stmt_4, axiom,
% 0.52/0.76    (![B:$i,A:$i]:
% 0.52/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.76  thf(zf_stmt_5, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.76  thf('7', plain,
% 0.52/0.76      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.76         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.52/0.76          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.52/0.76          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.52/0.76        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t24_relset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.52/0.76           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.52/0.76         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.52/0.76           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.76         (((k1_relset_1 @ X21 @ X20 @ (k3_relset_1 @ X20 @ X21 @ X22))
% 0.52/0.76            = (k2_relset_1 @ X20 @ X21 @ X22))
% 0.52/0.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.52/0.76      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.76         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.76  thf('13', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('14', plain,
% 0.52/0.76      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (sk_B))),
% 0.52/0.76      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.76         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.52/0.76          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.52/0.76          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      ((((sk_B) != (sk_B))
% 0.52/0.76        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.52/0.76        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 0.52/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.52/0.76        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.52/0.76      inference('simplify', [status(thm)], ['16'])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.76        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.52/0.76        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.52/0.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.52/0.76      inference('split', [status(esa)], ['18'])).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(cc1_relset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( v1_relat_1 @ C ) ))).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.76         ((v1_relat_1 @ X5)
% 0.52/0.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.52/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.76  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.76  thf(d9_funct_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.76       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (![X3 : $i]:
% 0.52/0.76         (~ (v2_funct_1 @ X3)
% 0.52/0.76          | ((k2_funct_1 @ X3) = (k4_relat_1 @ X3))
% 0.52/0.76          | ~ (v1_funct_1 @ X3)
% 0.52/0.76          | ~ (v1_relat_1 @ X3))),
% 0.52/0.76      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.76        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.52/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.76  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('26', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('27', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.52/0.76      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.52/0.76         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.52/0.76      inference('demod', [status(thm)], ['19', '27'])).
% 0.52/0.76  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.76  thf(dt_k2_funct_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.76       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.52/0.76         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.52/0.76  thf('30', plain,
% 0.52/0.76      (![X4 : $i]:
% 0.52/0.76         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.52/0.76          | ~ (v1_funct_1 @ X4)
% 0.52/0.76          | ~ (v1_relat_1 @ X4))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.76         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.76      inference('split', [status(esa)], ['18'])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.52/0.76         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.76  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.52/0.76  thf('35', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['29', '34'])).
% 0.52/0.76  thf('36', plain,
% 0.52/0.76      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.52/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.76      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.76  thf('37', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.52/0.76      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.52/0.76         <= (~
% 0.52/0.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.52/0.76      inference('split', [status(esa)], ['18'])).
% 0.52/0.76  thf('39', plain,
% 0.52/0.76      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.52/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.52/0.76         <= (~
% 0.52/0.76             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.52/0.76  thf('40', plain,
% 0.52/0.76      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['36', '39'])).
% 0.52/0.76  thf('41', plain,
% 0.52/0.76      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.52/0.76       ~
% 0.52/0.76       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.52/0.76       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['18'])).
% 0.52/0.76  thf('42', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['35', '40', '41'])).
% 0.52/0.76  thf('43', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['28', '42'])).
% 0.52/0.76  thf('44', plain, (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 0.52/0.76      inference('clc', [status(thm)], ['17', '43'])).
% 0.52/0.76  thf('45', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.52/0.76      inference('clc', [status(thm)], ['8', '44'])).
% 0.52/0.76  thf('46', plain,
% 0.52/0.76      (![X23 : $i, X24 : $i]:
% 0.52/0.76         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.52/0.76  thf('47', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.52/0.76      inference('clc', [status(thm)], ['8', '44'])).
% 0.52/0.76  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.76  thf('49', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_B)),
% 0.52/0.76      inference('demod', [status(thm)], ['45', '48'])).
% 0.52/0.76  thf('50', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.76  thf('51', plain,
% 0.52/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.76         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.52/0.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.52/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.76  thf('52', plain,
% 0.52/0.76      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.76  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('54', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.52/0.76      inference('sup+', [status(thm)], ['52', '53'])).
% 0.52/0.76  thf(t110_relat_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( v1_relat_1 @ A ) =>
% 0.52/0.76       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.76          | ~ (v1_relat_1 @ X0))),
% 0.52/0.76      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(cc2_relset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.76  thf('57', plain,
% 0.52/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.76         ((v4_relat_1 @ X8 @ X9)
% 0.52/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.52/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.76  thf('58', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.52/0.76      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.76  thf(t209_relat_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.76       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.76  thf('59', plain,
% 0.52/0.76      (![X1 : $i, X2 : $i]:
% 0.52/0.76         (((X1) = (k7_relat_1 @ X1 @ X2))
% 0.52/0.76          | ~ (v4_relat_1 @ X1 @ X2)
% 0.52/0.76          | ~ (v1_relat_1 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.76  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.76  thf('62', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)], ['60', '61'])).
% 0.52/0.76  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.76  thf('64', plain, (((sk_C) = (k7_relat_1 @ sk_C @ k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.76  thf('65', plain, ((((sk_C) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.76      inference('sup+', [status(thm)], ['55', '64'])).
% 0.52/0.76  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.76  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['65', '66'])).
% 0.52/0.76  thf('68', plain, (((k2_relat_1 @ k1_xboole_0) = (sk_B))),
% 0.52/0.76      inference('demod', [status(thm)], ['54', '67'])).
% 0.52/0.76  thf(t60_relat_1, axiom,
% 0.52/0.76    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.76     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.76  thf('69', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.76  thf('70', plain, (((sk_B) = (k1_xboole_0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['68', '69'])).
% 0.52/0.76  thf('71', plain,
% 0.52/0.76      (![X23 : $i, X24 : $i]:
% 0.52/0.76         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.52/0.76  thf('72', plain,
% 0.52/0.76      (![X23 : $i, X24 : $i]:
% 0.52/0.76         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.52/0.76  thf('73', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.52/0.76      inference('simplify', [status(thm)], ['72'])).
% 0.52/0.76  thf('74', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.52/0.76      inference('sup+', [status(thm)], ['71', '73'])).
% 0.52/0.76  thf('75', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.52/0.76      inference('eq_fact', [status(thm)], ['74'])).
% 0.52/0.76  thf('76', plain, ($false),
% 0.52/0.76      inference('demod', [status(thm)], ['49', '70', '75'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
