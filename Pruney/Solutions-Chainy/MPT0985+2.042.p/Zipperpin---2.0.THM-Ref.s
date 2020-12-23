%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7pOw3v1Kf3

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:32 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 662 expanded)
%              Number of leaves         :   41 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          : 1043 (10767 expanded)
%              Number of equality atoms :   48 ( 355 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X21 )
      | ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('8',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('26',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('35',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('40',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','38','39'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['26','40'])).

thf('42',plain,(
    ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B ) ),
    inference(clc,[status(thm)],['22','41'])).

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

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('60',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X34: $i] :
      ( ( v1_funct_2 @ X34 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['56','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','79'])).

thf('81',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['26','40'])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('85',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_partfun1 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('86',plain,
    ( ( v1_partfun1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('88',plain,
    ( ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('90',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['83','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7pOw3v1Kf3
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 230 iterations in 0.332s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.79  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.60/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.60/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.60/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.79  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.60/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.79  thf(t31_funct_2, conjecture,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.79       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.60/0.79         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.60/0.79           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.60/0.79           ( m1_subset_1 @
% 0.60/0.79             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.79            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.79          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.60/0.79            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.60/0.79              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.60/0.79              ( m1_subset_1 @
% 0.60/0.79                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.60/0.79  thf('0', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(dt_k3_relset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( m1_subset_1 @
% 0.60/0.79         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.60/0.79         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.60/0.79  thf('1', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.79         ((m1_subset_1 @ (k3_relset_1 @ X8 @ X9 @ X10) @ 
% 0.60/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.60/0.79          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.79  thf('3', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(redefinition_k3_relset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.60/0.79  thf('4', plain,
% 0.60/0.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.60/0.79         (((k3_relset_1 @ X18 @ X19 @ X17) = (k4_relat_1 @ X17))
% 0.60/0.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.60/0.79      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.60/0.79  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['2', '5'])).
% 0.60/0.79  thf(cc1_funct_2, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.60/0.79         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.60/0.79         (~ (v1_funct_1 @ X20)
% 0.60/0.79          | ~ (v1_partfun1 @ X20 @ X21)
% 0.60/0.79          | (v1_funct_2 @ X20 @ X21 @ X22)
% 0.60/0.79          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.60/0.79      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.60/0.79        | ~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B)
% 0.60/0.79        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.79  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(d9_funct_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      (![X1 : $i]:
% 0.60/0.79         (~ (v2_funct_1 @ X1)
% 0.60/0.79          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.60/0.79          | ~ (v1_funct_1 @ X1)
% 0.60/0.79          | ~ (v1_relat_1 @ X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.60/0.79  thf('11', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.60/0.79        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.60/0.79        | ~ (v2_funct_1 @ sk_C))),
% 0.60/0.79      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.79  thf('12', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(cc1_relset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( v1_relat_1 @ C ) ))).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         ((v1_relat_1 @ X5)
% 0.60/0.79          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.60/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.79  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.79  thf('15', plain, ((v2_funct_1 @ sk_C)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('16', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.60/0.79  thf(dt_k2_funct_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.60/0.79         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      (![X2 : $i]:
% 0.60/0.79         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.60/0.79          | ~ (v1_funct_1 @ X2)
% 0.60/0.79          | ~ (v1_relat_1 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.60/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_C))),
% 0.60/0.79      inference('sup+', [status(thm)], ['16', '17'])).
% 0.60/0.79  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.79  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('21', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.60/0.79        | ~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['8', '21'])).
% 0.60/0.79  thf('23', plain,
% 0.60/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.60/0.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.60/0.79        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.60/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.60/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['23'])).
% 0.60/0.79  thf('25', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.60/0.79  thf('26', plain,
% 0.60/0.79      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.60/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.60/0.79  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      (![X2 : $i]:
% 0.60/0.79         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.60/0.79          | ~ (v1_funct_1 @ X2)
% 0.60/0.79          | ~ (v1_relat_1 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.60/0.79         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.60/0.79      inference('split', [status(esa)], ['23'])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.60/0.79         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.79  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('32', plain,
% 0.60/0.79      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.60/0.79      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.79  thf('33', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['27', '32'])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['2', '5'])).
% 0.60/0.79  thf('35', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.60/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.60/0.79         <= (~
% 0.60/0.79             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.60/0.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.60/0.79      inference('split', [status(esa)], ['23'])).
% 0.60/0.79  thf('37', plain,
% 0.60/0.79      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.60/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.60/0.79         <= (~
% 0.60/0.79             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.60/0.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.60/0.79  thf('38', plain,
% 0.60/0.79      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.60/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['34', '37'])).
% 0.60/0.79  thf('39', plain,
% 0.60/0.79      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.60/0.79       ~
% 0.60/0.79       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.60/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.60/0.79       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.60/0.79      inference('split', [status(esa)], ['23'])).
% 0.60/0.79  thf('40', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.60/0.79      inference('sat_resolution*', [status(thm)], ['33', '38', '39'])).
% 0.60/0.79  thf('41', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['26', '40'])).
% 0.60/0.79  thf('42', plain, (~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B)),
% 0.60/0.79      inference('clc', [status(thm)], ['22', '41'])).
% 0.60/0.79  thf(d1_funct_2, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_1, axiom,
% 0.60/0.79    (![B:$i,A:$i]:
% 0.60/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.79  thf('43', plain,
% 0.60/0.79      (![X26 : $i, X27 : $i]:
% 0.60/0.79         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.79  thf('44', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.79  thf(zf_stmt_3, axiom,
% 0.60/0.79    (![C:$i,B:$i,A:$i]:
% 0.60/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.79  thf(zf_stmt_5, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.79  thf('45', plain,
% 0.60/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.60/0.79         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.60/0.79          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.60/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.79  thf('46', plain,
% 0.60/0.79      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.79  thf('47', plain,
% 0.60/0.79      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['43', '46'])).
% 0.60/0.79  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('49', plain,
% 0.60/0.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.79         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.60/0.79          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.60/0.79          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.79  thf('50', plain,
% 0.60/0.79      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.60/0.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.60/0.79  thf('51', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.79  thf('52', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.79         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.60/0.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.60/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.79  thf('53', plain,
% 0.60/0.79      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.60/0.79      inference('sup-', [status(thm)], ['51', '52'])).
% 0.60/0.79  thf('54', plain,
% 0.60/0.79      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.60/0.79      inference('demod', [status(thm)], ['50', '53'])).
% 0.60/0.79  thf('55', plain,
% 0.60/0.79      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['47', '54'])).
% 0.60/0.79  thf('56', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.60/0.79  thf(t55_funct_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ( v2_funct_1 @ A ) =>
% 0.60/0.79         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.60/0.79           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.60/0.79  thf('57', plain,
% 0.60/0.79      (![X4 : $i]:
% 0.60/0.79         (~ (v2_funct_1 @ X4)
% 0.60/0.79          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.60/0.79          | ~ (v1_funct_1 @ X4)
% 0.60/0.79          | ~ (v1_relat_1 @ X4))),
% 0.60/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.60/0.79  thf('58', plain,
% 0.60/0.79      (![X2 : $i]:
% 0.60/0.79         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.60/0.79          | ~ (v1_funct_1 @ X2)
% 0.60/0.79          | ~ (v1_relat_1 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.60/0.79  thf('59', plain,
% 0.60/0.79      (![X2 : $i]:
% 0.60/0.79         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.60/0.79          | ~ (v1_funct_1 @ X2)
% 0.60/0.79          | ~ (v1_relat_1 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.60/0.79  thf('60', plain,
% 0.60/0.79      (![X4 : $i]:
% 0.60/0.79         (~ (v2_funct_1 @ X4)
% 0.60/0.79          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.60/0.79          | ~ (v1_funct_1 @ X4)
% 0.60/0.79          | ~ (v1_relat_1 @ X4))),
% 0.60/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.60/0.79  thf(t3_funct_2, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.79       ( ( v1_funct_1 @ A ) & 
% 0.60/0.79         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.60/0.79         ( m1_subset_1 @
% 0.60/0.79           A @ 
% 0.60/0.79           ( k1_zfmisc_1 @
% 0.60/0.79             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.60/0.79  thf('61', plain,
% 0.60/0.79      (![X34 : $i]:
% 0.60/0.79         ((v1_funct_2 @ X34 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))
% 0.60/0.79          | ~ (v1_funct_1 @ X34)
% 0.60/0.79          | ~ (v1_relat_1 @ X34))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.60/0.79  thf('62', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.60/0.79           (k1_relat_1 @ X0))
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.60/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['60', '61'])).
% 0.60/0.79  thf('63', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.79          | ~ (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.60/0.79             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['59', '62'])).
% 0.60/0.79  thf('64', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.60/0.79           (k1_relat_1 @ X0))
% 0.60/0.79          | ~ (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['63'])).
% 0.60/0.79  thf('65', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v2_funct_1 @ X0)
% 0.60/0.79          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.60/0.79             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['58', '64'])).
% 0.60/0.79  thf('66', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.60/0.79           (k1_relat_1 @ X0))
% 0.60/0.79          | ~ (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['65'])).
% 0.60/0.79  thf('67', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.60/0.79           (k1_relat_1 @ X0))
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v2_funct_1 @ X0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['57', '66'])).
% 0.60/0.79  thf('68', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v2_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.60/0.79             (k1_relat_1 @ X0)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['67'])).
% 0.60/0.79  thf('69', plain,
% 0.60/0.79      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.60/0.79         (k1_relat_1 @ sk_C))
% 0.60/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.60/0.79        | ~ (v1_funct_1 @ sk_C)
% 0.60/0.79        | ~ (v2_funct_1 @ sk_C))),
% 0.60/0.79      inference('sup+', [status(thm)], ['56', '68'])).
% 0.60/0.79  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.60/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.79  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('73', plain,
% 0.60/0.79      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.60/0.79        (k1_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.60/0.79  thf('74', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.79  thf('75', plain,
% 0.60/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.79         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.60/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.60/0.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.79  thf('76', plain,
% 0.60/0.79      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.60/0.79      inference('sup-', [status(thm)], ['74', '75'])).
% 0.60/0.79  thf('77', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('78', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.60/0.79      inference('sup+', [status(thm)], ['76', '77'])).
% 0.60/0.79  thf('79', plain,
% 0.60/0.79      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.60/0.79      inference('demod', [status(thm)], ['73', '78'])).
% 0.60/0.79  thf('80', plain,
% 0.60/0.79      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.60/0.79        | ((sk_B) = (k1_xboole_0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['55', '79'])).
% 0.60/0.79  thf('81', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['26', '40'])).
% 0.60/0.79  thf('82', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.79      inference('clc', [status(thm)], ['80', '81'])).
% 0.60/0.79  thf('83', plain, (~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0)),
% 0.60/0.79      inference('demod', [status(thm)], ['42', '82'])).
% 0.60/0.79  thf('84', plain,
% 0.60/0.79      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.79  thf(cc1_partfun1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( v1_xboole_0 @ A ) =>
% 0.60/0.79       ( ![C:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.79           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.60/0.79  thf('85', plain,
% 0.60/0.79      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.79         (~ (v1_xboole_0 @ X23)
% 0.60/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 0.60/0.79          | (v1_partfun1 @ X24 @ X23))),
% 0.60/0.79      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.60/0.79  thf('86', plain,
% 0.60/0.79      (((v1_partfun1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.60/0.79        | ~ (v1_xboole_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['84', '85'])).
% 0.60/0.79  thf('87', plain,
% 0.60/0.79      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.60/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf('88', plain,
% 0.60/0.79      (((v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B) | ~ (v1_xboole_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['86', '87'])).
% 0.60/0.79  thf('89', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.79      inference('clc', [status(thm)], ['80', '81'])).
% 0.60/0.79  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.79      inference('clc', [status(thm)], ['80', '81'])).
% 0.60/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.79  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.79  thf('92', plain, ((v1_partfun1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0)),
% 0.60/0.79      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.60/0.79  thf('93', plain, ($false), inference('demod', [status(thm)], ['83', '92'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
