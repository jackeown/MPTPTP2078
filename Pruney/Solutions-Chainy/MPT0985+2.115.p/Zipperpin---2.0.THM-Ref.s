%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zaEV1vg44r

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:42 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 538 expanded)
%              Number of leaves         :   40 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          :  849 (8827 expanded)
%              Number of equality atoms :   56 ( 308 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_relset_1 @ X22 @ X23 @ X21 )
        = ( k4_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X24 @ ( k3_relset_1 @ X24 @ X25 @ X26 ) )
        = ( k2_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
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

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','24','25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('36',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('38',plain,
    ( ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('45',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['34','43','44'])).

thf('46',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['27','45'])).

thf('47',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','46'])).

thf('48',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','47'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('66',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('68',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('69',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['62','63','65','66','67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['57','69'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('71',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('72',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['52','72','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zaEV1vg44r
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 267 iterations in 0.173s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.62  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.40/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.62  thf(t31_funct_2, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.40/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.40/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.40/0.62           ( m1_subset_1 @
% 0.40/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.62          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.40/0.62            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.40/0.62              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.40/0.62              ( m1_subset_1 @
% 0.40/0.62                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(dt_k3_relset_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.62       ( m1_subset_1 @
% 0.40/0.62         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.40/0.62         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.62         ((m1_subset_1 @ (k3_relset_1 @ X15 @ X16 @ X17) @ 
% 0.40/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.40/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(redefinition_k3_relset_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.62       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (((k3_relset_1 @ X22 @ X23 @ X21) = (k4_relat_1 @ X21))
% 0.40/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.40/0.62  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.40/0.62  thf(d1_funct_2, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.62  thf(zf_stmt_2, axiom,
% 0.40/0.62    (![C:$i,B:$i,A:$i]:
% 0.40/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.62  thf(zf_stmt_4, axiom,
% 0.40/0.62    (![B:$i,A:$i]:
% 0.40/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.62  thf(zf_stmt_5, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.62         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.40/0.62          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.40/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.40/0.62        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t24_relset_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.62       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.40/0.62           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.40/0.62         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.40/0.62           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.62         (((k1_relset_1 @ X25 @ X24 @ (k3_relset_1 @ X24 @ X25 @ X26))
% 0.40/0.62            = (k2_relset_1 @ X24 @ X25 @ X26))
% 0.40/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.62      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.40/0.62         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf('13', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.62         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.40/0.62          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.40/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      ((((sk_B) != (sk_B))
% 0.40/0.62        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 0.40/0.62        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.40/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.62  thf(d9_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X10 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X10)
% 0.40/0.62          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.40/0.62          | ~ (v1_funct_1 @ X10)
% 0.40/0.62          | ~ (v1_relat_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.40/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.40/0.62      inference('split', [status(esa)], ['19'])).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62         | ~ (v2_funct_1 @ sk_C)))
% 0.40/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '20'])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(cc1_relset_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.62       ( v1_relat_1 @ C ) ))).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.62         ((v1_relat_1 @ X12)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.40/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.62  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('26', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.40/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['21', '24', '25', '26'])).
% 0.40/0.62  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf(dt_k2_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X11 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 0.40/0.62          | ~ (v1_funct_1 @ X11)
% 0.40/0.62          | ~ (v1_relat_1 @ X11))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('split', [status(esa)], ['19'])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.40/0.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('34', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['28', '33'])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      (![X10 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X10)
% 0.40/0.62          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.40/0.62          | ~ (v1_funct_1 @ X10)
% 0.40/0.62          | ~ (v1_relat_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.40/0.62  thf('37', plain,
% 0.40/0.62      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.40/0.62      inference('split', [status(esa)], ['19'])).
% 0.40/0.62  thf('38', plain,
% 0.40/0.62      (((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.40/0.62            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.40/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62         | ~ (v2_funct_1 @ sk_C)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.62  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.40/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['35', '42'])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.40/0.62       ~
% 0.40/0.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.40/0.62       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('split', [status(esa)], ['19'])).
% 0.40/0.62  thf('45', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['34', '43', '44'])).
% 0.40/0.62  thf('46', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['27', '45'])).
% 0.40/0.62  thf('47', plain, (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 0.40/0.62      inference('clc', [status(thm)], ['17', '46'])).
% 0.40/0.62  thf('48', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.40/0.62      inference('clc', [status(thm)], ['8', '47'])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      (![X27 : $i, X28 : $i]:
% 0.40/0.62         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.62  thf('50', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.40/0.62      inference('clc', [status(thm)], ['8', '47'])).
% 0.40/0.62  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.62  thf('52', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_B)),
% 0.40/0.62      inference('demod', [status(thm)], ['48', '51'])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.63  thf('54', plain,
% 0.40/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.63         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.40/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.63  thf('55', plain,
% 0.40/0.63      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.63  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.40/0.63      inference('sup+', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('58', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t3_subset, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.63  thf('59', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i]:
% 0.40/0.63         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.63  thf('60', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.63  thf(d10_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.63  thf('61', plain,
% 0.40/0.63      (![X0 : $i, X2 : $i]:
% 0.40/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.63  thf('62', plain,
% 0.40/0.63      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.40/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.63  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.63  thf(t113_zfmisc_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.63  thf('64', plain,
% 0.40/0.63      (![X5 : $i, X6 : $i]:
% 0.40/0.63         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.63  thf('65', plain,
% 0.40/0.63      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.40/0.63      inference('simplify', [status(thm)], ['64'])).
% 0.40/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.63  thf('66', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.40/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.63  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.63  thf('68', plain,
% 0.40/0.63      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.40/0.63      inference('simplify', [status(thm)], ['64'])).
% 0.40/0.63  thf('69', plain, (((k1_xboole_0) = (sk_C))),
% 0.40/0.63      inference('demod', [status(thm)], ['62', '63', '65', '66', '67', '68'])).
% 0.40/0.63  thf('70', plain, (((k2_relat_1 @ k1_xboole_0) = (sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['57', '69'])).
% 0.40/0.63  thf(t60_relat_1, axiom,
% 0.40/0.63    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.63     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.63  thf('71', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.63  thf('72', plain, (((sk_B) = (k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['70', '71'])).
% 0.40/0.63  thf('73', plain,
% 0.40/0.63      (![X27 : $i, X28 : $i]:
% 0.40/0.63         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.63  thf('74', plain,
% 0.40/0.63      (![X27 : $i, X28 : $i]:
% 0.40/0.63         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.63  thf('75', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.40/0.63      inference('simplify', [status(thm)], ['74'])).
% 0.40/0.63  thf('76', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.40/0.63      inference('sup+', [status(thm)], ['73', '75'])).
% 0.40/0.63  thf('77', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.40/0.63      inference('eq_fact', [status(thm)], ['76'])).
% 0.40/0.63  thf('78', plain, ($false),
% 0.40/0.63      inference('demod', [status(thm)], ['52', '72', '77'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
