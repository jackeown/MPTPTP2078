%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9HwNMyIKMn

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:33 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 678 expanded)
%              Number of leaves         :   40 ( 211 expanded)
%              Depth                    :   18
%              Number of atoms          :  834 (10467 expanded)
%              Number of equality atoms :   54 ( 357 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k3_relset_1 @ X16 @ X17 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X18 @ ( k3_relset_1 @ X18 @ X19 @ X20 ) )
        = ( k2_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
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
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('30',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','29'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('38',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['36','41','42'])).

thf('44',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','43'])).

thf('45',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','44'])).

thf('46',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','45'])).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('48',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','45'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 != k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ( X36 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X35 @ k1_xboole_0 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t25_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t25_relset_1])).

thf('54',plain,(
    ! [X35: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X35 @ k1_xboole_0 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','43'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('57',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X4: $i] :
      ( ( ( k7_relat_1 @ X4 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('65',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('67',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('70',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf(t66_relat_1,axiom,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('71',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t66_relat_1])).

thf('72',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','70','71'])).

thf('73',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','72'])).

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['50','73','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9HwNMyIKMn
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:47:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 309 iterations in 0.277s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.53/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.53/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.53/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.53/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.74  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(t31_funct_2, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.53/0.74         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.53/0.74           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.53/0.74           ( m1_subset_1 @
% 0.53/0.74             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.53/0.74            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.53/0.74              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.53/0.74              ( m1_subset_1 @
% 0.53/0.74                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(dt_k3_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( m1_subset_1 @
% 0.53/0.74         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.53/0.74         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k3_relset_1 @ X12 @ X13 @ X14) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12)))
% 0.53/0.74          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_k3_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.74         (((k3_relset_1 @ X16 @ X17 @ X15) = (k4_relat_1 @ X15))
% 0.53/0.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.53/0.74  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.74  thf(d1_funct_2, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.53/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.53/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.53/0.74  thf(zf_stmt_2, axiom,
% 0.53/0.74    (![C:$i,B:$i,A:$i]:
% 0.53/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.53/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.53/0.74  thf(zf_stmt_4, axiom,
% 0.53/0.74    (![B:$i,A:$i]:
% 0.53/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.53/0.74  thf(zf_stmt_5, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.53/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.53/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.53/0.74         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.53/0.74          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.53/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.53/0.74        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t24_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.53/0.74           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.53/0.74         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.53/0.74           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.74         (((k1_relset_1 @ X19 @ X18 @ (k3_relset_1 @ X18 @ X19 @ X20))
% 0.53/0.74            = (k2_relset_1 @ X18 @ X19 @ X20))
% 0.53/0.74          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.53/0.74      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.53/0.74         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.74  thf('13', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.74         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 0.53/0.74          | (v1_funct_2 @ X33 @ X31 @ X32)
% 0.53/0.74          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      ((((sk_B) != (sk_B))
% 0.53/0.74        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.53/0.74        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.53/0.74        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.53/0.74      inference('simplify', [status(thm)], ['16'])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.53/0.74        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.53/0.74        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.53/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.53/0.74         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d9_funct_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.74       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (![X7 : $i]:
% 0.53/0.74         (~ (v2_funct_1 @ X7)
% 0.53/0.74          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.53/0.74          | ~ (v1_funct_1 @ X7)
% 0.53/0.74          | ~ (v1_relat_1 @ X7))),
% 0.53/0.74      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.53/0.74        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.53/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(cc2_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.53/0.74          | (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.74  thf(fc6_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.74  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('28', plain, ((v2_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('29', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.53/0.74      inference('demod', [status(thm)], ['22', '27', '28'])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.53/0.74         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['19', '29'])).
% 0.53/0.74  thf(dt_k2_funct_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.74       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.53/0.74         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (![X8 : $i]:
% 0.53/0.74         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.53/0.74          | ~ (v1_funct_1 @ X8)
% 0.53/0.74          | ~ (v1_relat_1 @ X8))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.53/0.74         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.53/0.74         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('36', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.74  thf('38', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.53/0.74      inference('demod', [status(thm)], ['22', '27', '28'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.53/0.74         <= (~
% 0.53/0.74             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.53/0.74               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.53/0.74         <= (~
% 0.53/0.74             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.53/0.74               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['37', '40'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.53/0.74       ~
% 0.53/0.74       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.53/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.53/0.74       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('split', [status(esa)], ['18'])).
% 0.53/0.74  thf('43', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.53/0.74      inference('sat_resolution*', [status(thm)], ['36', '41', '42'])).
% 0.53/0.74  thf('44', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['30', '43'])).
% 0.53/0.74  thf('45', plain, (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 0.53/0.74      inference('clc', [status(thm)], ['17', '44'])).
% 0.53/0.74  thf('46', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.53/0.74      inference('clc', [status(thm)], ['8', '45'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (![X29 : $i, X30 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.53/0.74  thf('48', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.53/0.74      inference('clc', [status(thm)], ['8', '45'])).
% 0.53/0.74  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.74  thf('50', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_B)),
% 0.53/0.74      inference('demod', [status(thm)], ['46', '49'])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.53/0.74         (((X34) != (k1_xboole_0))
% 0.53/0.74          | ((X35) = (k1_xboole_0))
% 0.53/0.74          | (v1_funct_2 @ X36 @ X35 @ X34)
% 0.53/0.74          | ((X36) != (k1_xboole_0))
% 0.53/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (![X35 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.53/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ k1_xboole_0)))
% 0.53/0.74          | (v1_funct_2 @ k1_xboole_0 @ X35 @ k1_xboole_0)
% 0.53/0.74          | ((X35) = (k1_xboole_0)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['51'])).
% 0.53/0.74  thf(t25_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      (![X21 : $i, X22 : $i]:
% 0.53/0.74         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t25_relset_1])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      (![X35 : $i]:
% 0.53/0.74         ((v1_funct_2 @ k1_xboole_0 @ X35 @ k1_xboole_0)
% 0.53/0.74          | ((X35) = (k1_xboole_0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.53/0.74  thf('55', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['30', '43'])).
% 0.53/0.74  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.74  thf('57', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.53/0.74  thf(t110_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      (![X4 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))
% 0.53/0.74          | ~ (v1_relat_1 @ X4))),
% 0.53/0.74      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(cc2_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.74         ((v4_relat_1 @ X9 @ X10)
% 0.53/0.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.74  thf('61', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['59', '60'])).
% 0.53/0.74  thf(t209_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.53/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.53/0.74  thf('62', plain,
% 0.53/0.74      (![X5 : $i, X6 : $i]:
% 0.53/0.74         (((X5) = (k7_relat_1 @ X5 @ X6))
% 0.53/0.74          | ~ (v4_relat_1 @ X5 @ X6)
% 0.53/0.74          | ~ (v1_relat_1 @ X5))),
% 0.53/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.53/0.74  thf('63', plain,
% 0.53/0.74      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['61', '62'])).
% 0.53/0.74  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('65', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['63', '64'])).
% 0.53/0.74  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.74  thf('67', plain, (((sk_C) = (k7_relat_1 @ sk_C @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['65', '66'])).
% 0.53/0.74  thf('68', plain, ((((sk_C) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.53/0.74      inference('sup+', [status(thm)], ['58', '67'])).
% 0.53/0.74  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.74  thf('70', plain, (((sk_C) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf(t66_relat_1, axiom, (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.53/0.74  thf('71', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t66_relat_1])).
% 0.53/0.74  thf('72', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['57', '70', '71'])).
% 0.53/0.74  thf('73', plain, (((sk_B) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['54', '72'])).
% 0.53/0.74  thf('74', plain,
% 0.53/0.74      (![X29 : $i, X30 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.53/0.74  thf('75', plain,
% 0.53/0.74      (![X29 : $i, X30 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.53/0.74  thf('76', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 0.53/0.74      inference('simplify', [status(thm)], ['75'])).
% 0.53/0.74  thf('77', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.53/0.74      inference('sup+', [status(thm)], ['74', '76'])).
% 0.53/0.74  thf('78', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.53/0.74      inference('eq_fact', [status(thm)], ['77'])).
% 0.53/0.74  thf('79', plain, ($false),
% 0.53/0.74      inference('demod', [status(thm)], ['50', '73', '78'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
