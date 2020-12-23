%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.stui1q51Sz

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:46 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  264 (1728 expanded)
%              Number of leaves         :   50 ( 527 expanded)
%              Depth                    :   25
%              Number of atoms          : 2413 (44459 expanded)
%              Number of equality atoms :  173 (2351 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ( v1_partfun1 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X42 @ X40 )
      | ( v1_partfun1 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_partfun1 @ X39 @ X38 )
      | ( ( k1_relat_1 @ X39 )
        = X38 )
      | ~ ( v4_relat_1 @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('15',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X47: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('45',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X48 @ X50 )
       != X48 )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_tops_2 @ X49 @ X48 @ X50 )
        = ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('72',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','56','57','75'])).

thf('77',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('79',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','29','30','35','77','78'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t31_funct_2,axiom,(
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

thf('82',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('94',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('97',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('107',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','109'])).

thf('111',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','110'])).

thf('112',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('119',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['79','119'])).

thf('121',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X43 ) @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('132',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('133',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127','130','133','134'])).

thf('136',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

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

thf('141',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('145',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('146',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('149',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['143','151'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('157',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('158',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('160',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('163',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('164',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('167',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('168',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('169',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('170',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['169'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('171',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X26 ) ) )
      | ( v1_partfun1 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('172',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('174',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['168','174'])).

thf('176',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_partfun1 @ X39 @ X38 )
      | ( ( k1_relat_1 @ X39 )
        = X38 )
      | ~ ( v4_relat_1 @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('179',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('180',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('182',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('183',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['177','180','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['167','184'])).

thf('186',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['166','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','188'])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('195',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('196',plain,(
    ! [X47: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['194','198'])).

thf('200',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(clc,[status(thm)],['193','203'])).

thf('205',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','204'])).

thf('206',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','205'])).

thf('207',plain,(
    ( u1_struct_0 @ sk_B )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','206'])).

thf('208',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','207'])).

thf('209',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('210',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    $false ),
    inference(simplify,[status(thm)],['211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.stui1q51Sz
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.22/2.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.22/2.43  % Solved by: fo/fo7.sh
% 2.22/2.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.43  % done 2395 iterations in 1.970s
% 2.22/2.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.22/2.43  % SZS output start Refutation
% 2.22/2.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.22/2.43  thf(sk_C_type, type, sk_C: $i).
% 2.22/2.43  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.22/2.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.22/2.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.22/2.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.22/2.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.22/2.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.22/2.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.22/2.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.22/2.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.22/2.43  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.22/2.43  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.43  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.22/2.43  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.22/2.43  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.43  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.22/2.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.22/2.43  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.22/2.43  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.22/2.43  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.22/2.43  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.22/2.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.22/2.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.22/2.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.22/2.43  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.22/2.43  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.22/2.43  thf(d3_struct_0, axiom,
% 2.22/2.43    (![A:$i]:
% 2.22/2.43     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.22/2.43  thf('0', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('1', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf(t62_tops_2, conjecture,
% 2.22/2.43    (![A:$i]:
% 2.22/2.43     ( ( l1_struct_0 @ A ) =>
% 2.22/2.43       ( ![B:$i]:
% 2.22/2.43         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.22/2.43           ( ![C:$i]:
% 2.22/2.43             ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.43                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.22/2.43                 ( m1_subset_1 @
% 2.22/2.43                   C @ 
% 2.22/2.43                   ( k1_zfmisc_1 @
% 2.22/2.43                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.22/2.43               ( ( ( ( k2_relset_1 @
% 2.22/2.43                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.22/2.43                     ( k2_struct_0 @ B ) ) & 
% 2.22/2.43                   ( v2_funct_1 @ C ) ) =>
% 2.22/2.43                 ( ( ( k1_relset_1 @
% 2.22/2.43                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.22/2.43                       ( k2_tops_2 @
% 2.22/2.43                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.22/2.43                     ( k2_struct_0 @ B ) ) & 
% 2.22/2.43                   ( ( k2_relset_1 @
% 2.22/2.43                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.22/2.43                       ( k2_tops_2 @
% 2.22/2.43                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.22/2.43                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.22/2.43  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.43    (~( ![A:$i]:
% 2.22/2.43        ( ( l1_struct_0 @ A ) =>
% 2.22/2.43          ( ![B:$i]:
% 2.22/2.43            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.22/2.43              ( ![C:$i]:
% 2.22/2.43                ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.43                    ( v1_funct_2 @
% 2.22/2.43                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.22/2.43                    ( m1_subset_1 @
% 2.22/2.43                      C @ 
% 2.22/2.43                      ( k1_zfmisc_1 @
% 2.22/2.43                        ( k2_zfmisc_1 @
% 2.22/2.43                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.22/2.43                  ( ( ( ( k2_relset_1 @
% 2.22/2.43                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.22/2.43                        ( k2_struct_0 @ B ) ) & 
% 2.22/2.43                      ( v2_funct_1 @ C ) ) =>
% 2.22/2.43                    ( ( ( k1_relset_1 @
% 2.22/2.43                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.22/2.43                          ( k2_tops_2 @
% 2.22/2.43                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.22/2.43                        ( k2_struct_0 @ B ) ) & 
% 2.22/2.43                      ( ( k2_relset_1 @
% 2.22/2.43                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.22/2.43                          ( k2_tops_2 @
% 2.22/2.43                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.22/2.43                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.22/2.43    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 2.22/2.43  thf('2', plain,
% 2.22/2.43      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_B))
% 2.22/2.43        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43            != (k2_struct_0 @ sk_A)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('3', plain,
% 2.22/2.43      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_B)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_B))))),
% 2.22/2.43      inference('split', [status(esa)], ['2'])).
% 2.22/2.43  thf('4', plain,
% 2.22/2.43      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43           != (k2_struct_0 @ sk_B))
% 2.22/2.43         | ~ (l1_struct_0 @ sk_B)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_B))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['1', '3'])).
% 2.22/2.43  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('6', plain,
% 2.22/2.43      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_B)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_B))))),
% 2.22/2.43      inference('demod', [status(thm)], ['4', '5'])).
% 2.22/2.43  thf('7', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(t132_funct_2, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.43           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.22/2.43           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.22/2.43  thf('8', plain,
% 2.22/2.43      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.22/2.43         (((X40) = (k1_xboole_0))
% 2.22/2.43          | ~ (v1_funct_1 @ X41)
% 2.22/2.43          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 2.22/2.43          | (v1_partfun1 @ X41 @ X42)
% 2.22/2.43          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 2.22/2.43          | ~ (v1_funct_2 @ X41 @ X42 @ X40)
% 2.22/2.43          | ~ (v1_funct_1 @ X41))),
% 2.22/2.43      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.22/2.43  thf('9', plain,
% 2.22/2.43      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.22/2.43         (~ (v1_funct_2 @ X41 @ X42 @ X40)
% 2.22/2.43          | (v1_partfun1 @ X41 @ X42)
% 2.22/2.43          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 2.22/2.43          | ~ (v1_funct_1 @ X41)
% 2.22/2.43          | ((X40) = (k1_xboole_0)))),
% 2.22/2.43      inference('simplify', [status(thm)], ['8'])).
% 2.22/2.43  thf('10', plain,
% 2.22/2.43      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.22/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.22/2.43        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.22/2.43        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['7', '9'])).
% 2.22/2.43  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('12', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('13', plain,
% 2.22/2.43      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.22/2.43        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.22/2.43      inference('demod', [status(thm)], ['10', '11', '12'])).
% 2.22/2.43  thf(d4_partfun1, axiom,
% 2.22/2.43    (![A:$i,B:$i]:
% 2.22/2.43     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.22/2.43       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.22/2.43  thf('14', plain,
% 2.22/2.43      (![X38 : $i, X39 : $i]:
% 2.22/2.43         (~ (v1_partfun1 @ X39 @ X38)
% 2.22/2.43          | ((k1_relat_1 @ X39) = (X38))
% 2.22/2.43          | ~ (v4_relat_1 @ X39 @ X38)
% 2.22/2.43          | ~ (v1_relat_1 @ X39))),
% 2.22/2.43      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.22/2.43  thf('15', plain,
% 2.22/2.43      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.22/2.43        | ~ (v1_relat_1 @ sk_C)
% 2.22/2.43        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.22/2.43        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['13', '14'])).
% 2.22/2.43  thf('16', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(cc1_relset_1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43       ( v1_relat_1 @ C ) ))).
% 2.22/2.43  thf('17', plain,
% 2.22/2.43      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.22/2.43         ((v1_relat_1 @ X9)
% 2.22/2.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.22/2.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.22/2.43  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.43      inference('sup-', [status(thm)], ['16', '17'])).
% 2.22/2.43  thf('19', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(cc2_relset_1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.22/2.43  thf('20', plain,
% 2.22/2.43      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.22/2.43         ((v4_relat_1 @ X12 @ X13)
% 2.22/2.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.22/2.43      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.22/2.43  thf('21', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('sup-', [status(thm)], ['19', '20'])).
% 2.22/2.43  thf('22', plain,
% 2.22/2.43      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.22/2.43        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.22/2.43      inference('demod', [status(thm)], ['15', '18', '21'])).
% 2.22/2.43  thf(fc2_struct_0, axiom,
% 2.22/2.43    (![A:$i]:
% 2.22/2.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.22/2.43       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.22/2.43  thf('23', plain,
% 2.22/2.43      (![X47 : $i]:
% 2.22/2.43         (~ (v1_xboole_0 @ (u1_struct_0 @ X47))
% 2.22/2.43          | ~ (l1_struct_0 @ X47)
% 2.22/2.43          | (v2_struct_0 @ X47))),
% 2.22/2.43      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.22/2.43  thf('24', plain,
% 2.22/2.43      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.22/2.43        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 2.22/2.43        | (v2_struct_0 @ sk_B)
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup-', [status(thm)], ['22', '23'])).
% 2.22/2.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.22/2.43  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.22/2.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.22/2.43  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('27', plain,
% 2.22/2.43      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.22/2.43  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('29', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('30', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('31', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf(redefinition_k2_relset_1, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.22/2.43  thf('32', plain,
% 2.22/2.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.22/2.43         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 2.22/2.43          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.22/2.43  thf('33', plain,
% 2.22/2.43      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['31', '32'])).
% 2.22/2.43  thf('34', plain,
% 2.22/2.43      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('36', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('37', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('38', plain,
% 2.22/2.43      (((m1_subset_1 @ sk_C @ 
% 2.22/2.43         (k1_zfmisc_1 @ 
% 2.22/2.43          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['36', '37'])).
% 2.22/2.43  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('40', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.22/2.43      inference('demod', [status(thm)], ['38', '39'])).
% 2.22/2.43  thf('41', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('42', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.22/2.43      inference('demod', [status(thm)], ['40', '41'])).
% 2.22/2.43  thf('43', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('44', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.22/2.43      inference('demod', [status(thm)], ['42', '43'])).
% 2.22/2.43  thf(d4_tops_2, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.22/2.43         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.22/2.43  thf('45', plain,
% 2.22/2.43      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.22/2.43         (((k2_relset_1 @ X49 @ X48 @ X50) != (X48))
% 2.22/2.43          | ~ (v2_funct_1 @ X50)
% 2.22/2.43          | ((k2_tops_2 @ X49 @ X48 @ X50) = (k2_funct_1 @ X50))
% 2.22/2.43          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 2.22/2.43          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 2.22/2.43          | ~ (v1_funct_1 @ X50))),
% 2.22/2.43      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.22/2.43  thf('46', plain,
% 2.22/2.43      ((~ (v1_funct_1 @ sk_C)
% 2.22/2.43        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.22/2.43        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43            = (k2_funct_1 @ sk_C))
% 2.22/2.43        | ~ (v2_funct_1 @ sk_C)
% 2.22/2.43        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43            != (k2_relat_1 @ sk_C)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['44', '45'])).
% 2.22/2.43  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('48', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('49', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('50', plain,
% 2.22/2.43      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['48', '49'])).
% 2.22/2.43  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('52', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['50', '51'])).
% 2.22/2.43  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('54', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['52', '53'])).
% 2.22/2.43  thf('55', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('56', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['54', '55'])).
% 2.22/2.43  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('58', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('59', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('60', plain,
% 2.22/2.43      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('61', plain,
% 2.22/2.43      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43          = (k2_struct_0 @ sk_B))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['59', '60'])).
% 2.22/2.43  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('63', plain,
% 2.22/2.43      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['61', '62'])).
% 2.22/2.43  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('66', plain,
% 2.22/2.43      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.22/2.43  thf('67', plain,
% 2.22/2.43      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43          = (k2_relat_1 @ sk_C))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_A))),
% 2.22/2.43      inference('sup+', [status(thm)], ['58', '66'])).
% 2.22/2.43  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('69', plain,
% 2.22/2.43      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['67', '68'])).
% 2.22/2.43  thf('70', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('71', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('72', plain,
% 2.22/2.43      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.22/2.43      inference('sup+', [status(thm)], ['70', '71'])).
% 2.22/2.43  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('74', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.22/2.43      inference('demod', [status(thm)], ['72', '73'])).
% 2.22/2.43  thf('75', plain,
% 2.22/2.43      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['69', '74'])).
% 2.22/2.43  thf('76', plain,
% 2.22/2.43      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43          = (k2_funct_1 @ sk_C))
% 2.22/2.43        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.22/2.43      inference('demod', [status(thm)], ['46', '47', '56', '57', '75'])).
% 2.22/2.43  thf('77', plain,
% 2.22/2.43      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43         = (k2_funct_1 @ sk_C))),
% 2.22/2.43      inference('simplify', [status(thm)], ['76'])).
% 2.22/2.43  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('79', plain,
% 2.22/2.43      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_B))))),
% 2.22/2.43      inference('demod', [status(thm)], ['6', '29', '30', '35', '77', '78'])).
% 2.22/2.43  thf(t55_funct_1, axiom,
% 2.22/2.43    (![A:$i]:
% 2.22/2.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.43       ( ( v2_funct_1 @ A ) =>
% 2.22/2.43         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.22/2.43           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.22/2.43  thf('80', plain,
% 2.22/2.43      (![X8 : $i]:
% 2.22/2.43         (~ (v2_funct_1 @ X8)
% 2.22/2.43          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 2.22/2.43          | ~ (v1_funct_1 @ X8)
% 2.22/2.43          | ~ (v1_relat_1 @ X8))),
% 2.22/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.43  thf('81', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.22/2.43      inference('demod', [status(thm)], ['42', '43'])).
% 2.22/2.43  thf(t31_funct_2, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.43       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.22/2.43         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.22/2.43           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.22/2.43           ( m1_subset_1 @
% 2.22/2.43             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.22/2.43  thf('82', plain,
% 2.22/2.43      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.22/2.43         (~ (v2_funct_1 @ X43)
% 2.22/2.43          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 2.22/2.43          | (m1_subset_1 @ (k2_funct_1 @ X43) @ 
% 2.22/2.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.22/2.43          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.22/2.43          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 2.22/2.43          | ~ (v1_funct_1 @ X43))),
% 2.22/2.43      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.22/2.43  thf('83', plain,
% 2.22/2.43      ((~ (v1_funct_1 @ sk_C)
% 2.22/2.43        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.22/2.43        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43           (k1_zfmisc_1 @ 
% 2.22/2.43            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 2.22/2.43        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43            != (k2_relat_1 @ sk_C))
% 2.22/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['81', '82'])).
% 2.22/2.43  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('85', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['54', '55'])).
% 2.22/2.43  thf('86', plain,
% 2.22/2.43      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['69', '74'])).
% 2.22/2.43  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('88', plain,
% 2.22/2.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43         (k1_zfmisc_1 @ 
% 2.22/2.43          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 2.22/2.43        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.22/2.43      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 2.22/2.43  thf('89', plain,
% 2.22/2.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.22/2.43      inference('simplify', [status(thm)], ['88'])).
% 2.22/2.43  thf('90', plain,
% 2.22/2.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.22/2.43         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 2.22/2.43          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.22/2.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.22/2.43  thf('91', plain,
% 2.22/2.43      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['89', '90'])).
% 2.22/2.43  thf('92', plain,
% 2.22/2.43      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.22/2.43         = (k2_funct_1 @ sk_C))),
% 2.22/2.43      inference('simplify', [status(thm)], ['76'])).
% 2.22/2.43  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('94', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('95', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('96', plain,
% 2.22/2.43      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_A)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('split', [status(esa)], ['2'])).
% 2.22/2.43  thf('97', plain,
% 2.22/2.43      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43           != (k2_struct_0 @ sk_A))
% 2.22/2.43         | ~ (l1_struct_0 @ sk_B)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['95', '96'])).
% 2.22/2.43  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('99', plain,
% 2.22/2.43      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_A)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('demod', [status(thm)], ['97', '98'])).
% 2.22/2.43  thf('100', plain,
% 2.22/2.43      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43           != (k2_struct_0 @ sk_A))
% 2.22/2.43         | ~ (l1_struct_0 @ sk_B)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['94', '99'])).
% 2.22/2.43  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('102', plain,
% 2.22/2.43      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_A)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('demod', [status(thm)], ['100', '101'])).
% 2.22/2.43  thf('103', plain,
% 2.22/2.43      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_A)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['93', '102'])).
% 2.22/2.43  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('105', plain,
% 2.22/2.43      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.22/2.43          != (k2_struct_0 @ sk_A)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('demod', [status(thm)], ['103', '104'])).
% 2.22/2.43  thf('106', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('107', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('108', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.22/2.43      inference('demod', [status(thm)], ['72', '73'])).
% 2.22/2.43  thf('109', plain,
% 2.22/2.43      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.22/2.43          != (k1_relat_1 @ sk_C)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 2.22/2.43  thf('110', plain,
% 2.22/2.43      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['92', '109'])).
% 2.22/2.43  thf('111', plain,
% 2.22/2.43      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['91', '110'])).
% 2.22/2.43  thf('112', plain,
% 2.22/2.43      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 2.22/2.43         | ~ (v1_relat_1 @ sk_C)
% 2.22/2.43         | ~ (v1_funct_1 @ sk_C)
% 2.22/2.43         | ~ (v2_funct_1 @ sk_C)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['80', '111'])).
% 2.22/2.43  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.43      inference('sup-', [status(thm)], ['16', '17'])).
% 2.22/2.43  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('116', plain,
% 2.22/2.43      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 2.22/2.43         <= (~
% 2.22/2.43             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43                = (k2_struct_0 @ sk_A))))),
% 2.22/2.43      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 2.22/2.43  thf('117', plain,
% 2.22/2.43      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          = (k2_struct_0 @ sk_A)))),
% 2.22/2.43      inference('simplify', [status(thm)], ['116'])).
% 2.22/2.43  thf('118', plain,
% 2.22/2.43      (~
% 2.22/2.43       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          = (k2_struct_0 @ sk_B))) | 
% 2.22/2.43       ~
% 2.22/2.43       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          = (k2_struct_0 @ sk_A)))),
% 2.22/2.43      inference('split', [status(esa)], ['2'])).
% 2.22/2.43  thf('119', plain,
% 2.22/2.43      (~
% 2.22/2.43       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.22/2.43          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.22/2.43          = (k2_struct_0 @ sk_B)))),
% 2.22/2.43      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 2.22/2.43  thf('120', plain,
% 2.22/2.43      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('simpl_trail', [status(thm)], ['79', '119'])).
% 2.22/2.43  thf('121', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('122', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('123', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('124', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('demod', [status(thm)], ['122', '123'])).
% 2.22/2.43  thf('125', plain,
% 2.22/2.43      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.22/2.43         (~ (v2_funct_1 @ X43)
% 2.22/2.43          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 2.22/2.43          | (v1_funct_2 @ (k2_funct_1 @ X43) @ X44 @ X45)
% 2.22/2.43          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.22/2.43          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 2.22/2.43          | ~ (v1_funct_1 @ X43))),
% 2.22/2.43      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.22/2.43  thf('126', plain,
% 2.22/2.43      ((~ (v1_funct_1 @ sk_C)
% 2.22/2.43        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 2.22/2.43        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.22/2.43           (k1_relat_1 @ sk_C))
% 2.22/2.43        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43            != (u1_struct_0 @ sk_B))
% 2.22/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['124', '125'])).
% 2.22/2.43  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('128', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('129', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('130', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['128', '129'])).
% 2.22/2.43  thf('131', plain,
% 2.22/2.43      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['31', '32'])).
% 2.22/2.43  thf('132', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.22/2.43      inference('clc', [status(thm)], ['27', '28'])).
% 2.22/2.43  thf('133', plain,
% 2.22/2.43      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['131', '132'])).
% 2.22/2.43  thf('134', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('135', plain,
% 2.22/2.43      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.22/2.43         (k1_relat_1 @ sk_C))
% 2.22/2.43        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 2.22/2.43      inference('demod', [status(thm)], ['126', '127', '130', '133', '134'])).
% 2.22/2.43  thf('136', plain,
% 2.22/2.43      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B)
% 2.22/2.43        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.22/2.43           (k1_relat_1 @ sk_C)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['121', '135'])).
% 2.22/2.43  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('139', plain,
% 2.22/2.43      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 2.22/2.43        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.22/2.43           (k1_relat_1 @ sk_C)))),
% 2.22/2.43      inference('demod', [status(thm)], ['136', '137', '138'])).
% 2.22/2.43  thf('140', plain,
% 2.22/2.43      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.22/2.43        (k1_relat_1 @ sk_C))),
% 2.22/2.43      inference('simplify', [status(thm)], ['139'])).
% 2.22/2.43  thf(d1_funct_2, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.22/2.43           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.22/2.43             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.22/2.43         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.22/2.43           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.22/2.43             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.22/2.43  thf(zf_stmt_1, axiom,
% 2.22/2.43    (![C:$i,B:$i,A:$i]:
% 2.22/2.43     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.22/2.43       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.22/2.43  thf('141', plain,
% 2.22/2.43      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.22/2.43         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 2.22/2.43          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 2.22/2.43          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.43  thf('142', plain,
% 2.22/2.43      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43           (u1_struct_0 @ sk_B))
% 2.22/2.43        | ((u1_struct_0 @ sk_B)
% 2.22/2.43            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43               (k2_funct_1 @ sk_C))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['140', '141'])).
% 2.22/2.43  thf('143', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('144', plain,
% 2.22/2.43      ((m1_subset_1 @ sk_C @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 2.22/2.43      inference('demod', [status(thm)], ['122', '123'])).
% 2.22/2.43  thf('145', plain,
% 2.22/2.43      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.22/2.43         (~ (v2_funct_1 @ X43)
% 2.22/2.43          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 2.22/2.43          | (m1_subset_1 @ (k2_funct_1 @ X43) @ 
% 2.22/2.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.22/2.43          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.22/2.43          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 2.22/2.43          | ~ (v1_funct_1 @ X43))),
% 2.22/2.43      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.22/2.43  thf('146', plain,
% 2.22/2.43      ((~ (v1_funct_1 @ sk_C)
% 2.22/2.43        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 2.22/2.43        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43           (k1_zfmisc_1 @ 
% 2.22/2.43            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 2.22/2.43        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43            != (u1_struct_0 @ sk_B))
% 2.22/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.22/2.43      inference('sup-', [status(thm)], ['144', '145'])).
% 2.22/2.43  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('148', plain,
% 2.22/2.43      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['128', '129'])).
% 2.22/2.43  thf('149', plain,
% 2.22/2.43      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.22/2.43         = (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['131', '132'])).
% 2.22/2.43  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('151', plain,
% 2.22/2.43      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43         (k1_zfmisc_1 @ 
% 2.22/2.43          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 2.22/2.43        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 2.22/2.43      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 2.22/2.43  thf('152', plain,
% 2.22/2.43      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B)
% 2.22/2.43        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43           (k1_zfmisc_1 @ 
% 2.22/2.43            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 2.22/2.43      inference('sup-', [status(thm)], ['143', '151'])).
% 2.22/2.43  thf('153', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('155', plain,
% 2.22/2.43      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 2.22/2.43        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43           (k1_zfmisc_1 @ 
% 2.22/2.43            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 2.22/2.43      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.22/2.43  thf('156', plain,
% 2.22/2.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 2.22/2.43      inference('simplify', [status(thm)], ['155'])).
% 2.22/2.43  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.22/2.43  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.22/2.43  thf(zf_stmt_4, axiom,
% 2.22/2.43    (![B:$i,A:$i]:
% 2.22/2.43     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.22/2.43       ( zip_tseitin_0 @ B @ A ) ))).
% 2.22/2.43  thf(zf_stmt_5, axiom,
% 2.22/2.43    (![A:$i,B:$i,C:$i]:
% 2.22/2.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.22/2.43         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.22/2.43           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.22/2.43             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.22/2.43  thf('157', plain,
% 2.22/2.43      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.22/2.43         (~ (zip_tseitin_0 @ X35 @ X36)
% 2.22/2.43          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 2.22/2.43          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.22/2.43  thf('158', plain,
% 2.22/2.43      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43         (u1_struct_0 @ sk_B))
% 2.22/2.43        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['156', '157'])).
% 2.22/2.43  thf('159', plain,
% 2.22/2.43      (![X30 : $i, X31 : $i]:
% 2.22/2.43         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.22/2.43  thf('160', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.22/2.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.22/2.43  thf('161', plain,
% 2.22/2.43      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.22/2.43      inference('sup+', [status(thm)], ['159', '160'])).
% 2.22/2.43  thf('162', plain,
% 2.22/2.43      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.43        (k1_zfmisc_1 @ 
% 2.22/2.43         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.22/2.43      inference('simplify', [status(thm)], ['88'])).
% 2.22/2.43  thf(cc4_relset_1, axiom,
% 2.22/2.43    (![A:$i,B:$i]:
% 2.22/2.43     ( ( v1_xboole_0 @ A ) =>
% 2.22/2.43       ( ![C:$i]:
% 2.22/2.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.22/2.43           ( v1_xboole_0 @ C ) ) ) ))).
% 2.22/2.43  thf('163', plain,
% 2.22/2.43      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.22/2.43         (~ (v1_xboole_0 @ X18)
% 2.22/2.43          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 2.22/2.43          | (v1_xboole_0 @ X19))),
% 2.22/2.43      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.22/2.43  thf('164', plain,
% 2.22/2.43      (((v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 2.22/2.43        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['162', '163'])).
% 2.22/2.43  thf('165', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         ((zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)
% 2.22/2.43          | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['161', '164'])).
% 2.22/2.43  thf('166', plain,
% 2.22/2.43      (![X8 : $i]:
% 2.22/2.43         (~ (v2_funct_1 @ X8)
% 2.22/2.43          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 2.22/2.43          | ~ (v1_funct_1 @ X8)
% 2.22/2.43          | ~ (v1_relat_1 @ X8))),
% 2.22/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.43  thf(l13_xboole_0, axiom,
% 2.22/2.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.22/2.43  thf('167', plain,
% 2.22/2.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.22/2.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.22/2.43  thf(t4_subset_1, axiom,
% 2.22/2.43    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.22/2.43  thf('168', plain,
% 2.22/2.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 2.22/2.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.22/2.43  thf(t113_zfmisc_1, axiom,
% 2.22/2.43    (![A:$i,B:$i]:
% 2.22/2.43     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.22/2.43       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.22/2.43  thf('169', plain,
% 2.22/2.43      (![X2 : $i, X3 : $i]:
% 2.22/2.43         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 2.22/2.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.22/2.43  thf('170', plain,
% 2.22/2.43      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.22/2.43      inference('simplify', [status(thm)], ['169'])).
% 2.22/2.43  thf(cc1_partfun1, axiom,
% 2.22/2.43    (![A:$i,B:$i]:
% 2.22/2.43     ( ( v1_xboole_0 @ A ) =>
% 2.22/2.43       ( ![C:$i]:
% 2.22/2.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.43           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.22/2.43  thf('171', plain,
% 2.22/2.43      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.22/2.43         (~ (v1_xboole_0 @ X24)
% 2.22/2.43          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X26)))
% 2.22/2.43          | (v1_partfun1 @ X25 @ X24))),
% 2.22/2.43      inference('cnf', [status(esa)], [cc1_partfun1])).
% 2.22/2.43  thf('172', plain,
% 2.22/2.43      (![X1 : $i]:
% 2.22/2.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.43          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 2.22/2.43          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.22/2.43      inference('sup-', [status(thm)], ['170', '171'])).
% 2.22/2.43  thf('173', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.22/2.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.22/2.43  thf('174', plain,
% 2.22/2.43      (![X1 : $i]:
% 2.22/2.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.43          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 2.22/2.43      inference('demod', [status(thm)], ['172', '173'])).
% 2.22/2.43  thf('175', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 2.22/2.43      inference('sup-', [status(thm)], ['168', '174'])).
% 2.22/2.43  thf('176', plain,
% 2.22/2.43      (![X38 : $i, X39 : $i]:
% 2.22/2.43         (~ (v1_partfun1 @ X39 @ X38)
% 2.22/2.43          | ((k1_relat_1 @ X39) = (X38))
% 2.22/2.43          | ~ (v4_relat_1 @ X39 @ X38)
% 2.22/2.43          | ~ (v1_relat_1 @ X39))),
% 2.22/2.43      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.22/2.43  thf('177', plain,
% 2.22/2.43      ((~ (v1_relat_1 @ k1_xboole_0)
% 2.22/2.43        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 2.22/2.43        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['175', '176'])).
% 2.22/2.43  thf('178', plain,
% 2.22/2.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 2.22/2.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.22/2.43  thf('179', plain,
% 2.22/2.43      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.22/2.43         ((v1_relat_1 @ X9)
% 2.22/2.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.22/2.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.22/2.43  thf('180', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.22/2.43      inference('sup-', [status(thm)], ['178', '179'])).
% 2.22/2.43  thf('181', plain,
% 2.22/2.43      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 2.22/2.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.22/2.43  thf('182', plain,
% 2.22/2.43      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.22/2.43         ((v4_relat_1 @ X12 @ X13)
% 2.22/2.43          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.22/2.43      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.22/2.43  thf('183', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 2.22/2.43      inference('sup-', [status(thm)], ['181', '182'])).
% 2.22/2.43  thf('184', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.43      inference('demod', [status(thm)], ['177', '180', '183'])).
% 2.22/2.43  thf('185', plain,
% 2.22/2.43      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.22/2.43      inference('sup+', [status(thm)], ['167', '184'])).
% 2.22/2.43  thf('186', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.22/2.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.22/2.43  thf('187', plain,
% 2.22/2.43      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.22/2.43      inference('sup+', [status(thm)], ['185', '186'])).
% 2.22/2.43  thf('188', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         ((v1_xboole_0 @ (k2_relat_1 @ X0))
% 2.22/2.43          | ~ (v1_relat_1 @ X0)
% 2.22/2.43          | ~ (v1_funct_1 @ X0)
% 2.22/2.43          | ~ (v2_funct_1 @ X0)
% 2.22/2.43          | ~ (v1_xboole_0 @ (k2_funct_1 @ X0)))),
% 2.22/2.43      inference('sup+', [status(thm)], ['166', '187'])).
% 2.22/2.43  thf('189', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         ((zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)
% 2.22/2.43          | ~ (v2_funct_1 @ sk_C)
% 2.22/2.43          | ~ (v1_funct_1 @ sk_C)
% 2.22/2.43          | ~ (v1_relat_1 @ sk_C)
% 2.22/2.43          | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 2.22/2.43      inference('sup-', [status(thm)], ['165', '188'])).
% 2.22/2.43  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.43      inference('sup-', [status(thm)], ['16', '17'])).
% 2.22/2.43  thf('193', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         ((zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)
% 2.22/2.43          | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 2.22/2.43      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 2.22/2.43  thf('194', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('195', plain,
% 2.22/2.43      (![X46 : $i]:
% 2.22/2.43         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 2.22/2.43      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.22/2.43  thf('196', plain,
% 2.22/2.43      (![X47 : $i]:
% 2.22/2.43         (~ (v1_xboole_0 @ (u1_struct_0 @ X47))
% 2.22/2.43          | ~ (l1_struct_0 @ X47)
% 2.22/2.43          | (v2_struct_0 @ X47))),
% 2.22/2.43      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.22/2.43  thf('197', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.22/2.43          | ~ (l1_struct_0 @ X0)
% 2.22/2.43          | (v2_struct_0 @ X0)
% 2.22/2.43          | ~ (l1_struct_0 @ X0))),
% 2.22/2.43      inference('sup-', [status(thm)], ['195', '196'])).
% 2.22/2.43  thf('198', plain,
% 2.22/2.43      (![X0 : $i]:
% 2.22/2.43         ((v2_struct_0 @ X0)
% 2.22/2.43          | ~ (l1_struct_0 @ X0)
% 2.22/2.43          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 2.22/2.43      inference('simplify', [status(thm)], ['197'])).
% 2.22/2.43  thf('199', plain,
% 2.22/2.43      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.22/2.43        | ~ (l1_struct_0 @ sk_B)
% 2.22/2.43        | (v2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup-', [status(thm)], ['194', '198'])).
% 2.22/2.43  thf('200', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('201', plain,
% 2.22/2.43      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['199', '200'])).
% 2.22/2.43  thf('202', plain, (~ (v2_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('203', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('clc', [status(thm)], ['201', '202'])).
% 2.22/2.43  thf('204', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 2.22/2.43      inference('clc', [status(thm)], ['193', '203'])).
% 2.22/2.43  thf('205', plain,
% 2.22/2.43      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43        (u1_struct_0 @ sk_B))),
% 2.22/2.43      inference('demod', [status(thm)], ['158', '204'])).
% 2.22/2.43  thf('206', plain,
% 2.22/2.43      (((u1_struct_0 @ sk_B)
% 2.22/2.43         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 2.22/2.43            (k2_funct_1 @ sk_C)))),
% 2.22/2.43      inference('demod', [status(thm)], ['142', '205'])).
% 2.22/2.43  thf('207', plain, (((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['120', '206'])).
% 2.22/2.43  thf('208', plain,
% 2.22/2.43      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup-', [status(thm)], ['0', '207'])).
% 2.22/2.43  thf('209', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.22/2.43      inference('sup+', [status(thm)], ['33', '34'])).
% 2.22/2.43  thf('210', plain, ((l1_struct_0 @ sk_B)),
% 2.22/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.43  thf('211', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 2.22/2.43      inference('demod', [status(thm)], ['208', '209', '210'])).
% 2.22/2.43  thf('212', plain, ($false), inference('simplify', [status(thm)], ['211'])).
% 2.22/2.43  
% 2.22/2.43  % SZS output end Refutation
% 2.22/2.43  
% 2.22/2.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
