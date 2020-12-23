%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YWMxf2QDzn

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:54 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 384 expanded)
%              Number of leaves         :   39 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          : 1690 (9545 expanded)
%              Number of equality atoms :  121 ( 532 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','37','38','43'])).

thf('45',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X7 @ ( k3_relset_1 @ X7 @ X8 @ X9 ) )
        = ( k1_relset_1 @ X7 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_relset_1 @ X5 @ X6 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('63',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('70',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','73'])).

thf('75',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','73'])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X7 @ ( k3_relset_1 @ X7 @ X8 @ X9 ) )
        = ( k1_relset_1 @ X7 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('97',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_relset_1 @ X5 @ X6 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('98',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('100',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['84','101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','103'])).

thf('105',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('107',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('109',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X7 @ ( k3_relset_1 @ X7 @ X8 @ X9 ) )
        = ( k2_relset_1 @ X7 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('115',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','72'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','118'])).

thf('120',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('122',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['105','122'])).

thf('124',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','123'])).

thf('125',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','124'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('126',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['0','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YWMxf2QDzn
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 366 iterations in 0.478s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.94  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.94  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.76/0.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.94  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.76/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.94  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.76/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.94  thf(t62_tops_2, conjecture,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( l1_struct_0 @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.94           ( ![C:$i]:
% 0.76/0.94             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.94                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                 ( m1_subset_1 @
% 0.76/0.94                   C @ 
% 0.76/0.94                   ( k1_zfmisc_1 @
% 0.76/0.94                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.94               ( ( ( ( k2_relset_1 @
% 0.76/0.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.94                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.94                   ( v2_funct_1 @ C ) ) =>
% 0.76/0.94                 ( ( ( k1_relset_1 @
% 0.76/0.94                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.94                       ( k2_tops_2 @
% 0.76/0.94                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.94                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.94                   ( ( k2_relset_1 @
% 0.76/0.94                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.94                       ( k2_tops_2 @
% 0.76/0.94                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.94                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i]:
% 0.76/0.94        ( ( l1_struct_0 @ A ) =>
% 0.76/0.94          ( ![B:$i]:
% 0.76/0.94            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.94              ( ![C:$i]:
% 0.76/0.94                ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.94                    ( v1_funct_2 @
% 0.76/0.94                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                    ( m1_subset_1 @
% 0.76/0.94                      C @ 
% 0.76/0.94                      ( k1_zfmisc_1 @
% 0.76/0.94                        ( k2_zfmisc_1 @
% 0.76/0.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.94                  ( ( ( ( k2_relset_1 @
% 0.76/0.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.94                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.94                      ( v2_funct_1 @ C ) ) =>
% 0.76/0.94                    ( ( ( k1_relset_1 @
% 0.76/0.94                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.94                          ( k2_tops_2 @
% 0.76/0.94                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.94                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.94                      ( ( k2_relset_1 @
% 0.76/0.94                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.94                          ( k2_tops_2 @
% 0.76/0.94                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.94                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.76/0.94  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(d3_struct_0, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.76/0.94  thf('1', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf(d1_funct_2, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_1, axiom,
% 0.76/0.94    (![B:$i,A:$i]:
% 0.76/0.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.94       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.94  thf('3', plain,
% 0.76/0.94      (![X10 : $i, X11 : $i]:
% 0.76/0.94         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.94  thf(zf_stmt_3, axiom,
% 0.76/0.94    (![C:$i,B:$i,A:$i]:
% 0.76/0.94     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.94  thf(zf_stmt_5, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.94       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.94  thf('5', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.94         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.76/0.94          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.76/0.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.94  thf('6', plain,
% 0.76/0.94      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.94        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.94  thf('7', plain,
% 0.76/0.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.94        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['3', '6'])).
% 0.76/0.94  thf('8', plain,
% 0.76/0.94      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B)
% 0.76/0.94        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['2', '7'])).
% 0.76/0.94  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('10', plain,
% 0.76/0.94      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.94        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['8', '9'])).
% 0.76/0.94  thf('11', plain,
% 0.76/0.94      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A)
% 0.76/0.94        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['1', '10'])).
% 0.76/0.94  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('13', plain,
% 0.76/0.94      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.76/0.94        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['11', '12'])).
% 0.76/0.94  thf('14', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('16', plain,
% 0.76/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('17', plain,
% 0.76/0.94      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['15', '16'])).
% 0.76/0.94  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('19', plain,
% 0.76/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.94  thf('20', plain,
% 0.76/0.94      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['14', '19'])).
% 0.76/0.94  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('22', plain,
% 0.76/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.94  thf('23', plain,
% 0.76/0.94      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.76/0.94         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.76/0.94          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.76/0.94          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.94  thf('24', plain,
% 0.76/0.94      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.76/0.94        | ((k2_struct_0 @ sk_A)
% 0.76/0.94            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.94  thf('25', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('27', plain,
% 0.76/0.94      (((m1_subset_1 @ sk_C @ 
% 0.76/0.94         (k1_zfmisc_1 @ 
% 0.76/0.94          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['25', '26'])).
% 0.76/0.94  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('29', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.94  thf(d4_tops_2, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.94       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.76/0.94         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.76/0.94  thf('30', plain,
% 0.76/0.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.94         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.76/0.94          | ~ (v2_funct_1 @ X22)
% 0.76/0.94          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.76/0.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.76/0.94          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.76/0.94          | ~ (v1_funct_1 @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.94        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94            = (k2_funct_1 @ sk_C))
% 0.76/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.94        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94            != (k2_struct_0 @ sk_B)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/0.94  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('33', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('34', plain,
% 0.76/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/0.94  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('37', plain,
% 0.76/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['35', '36'])).
% 0.76/0.94  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('39', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('40', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_struct_0 @ sk_B))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('41', plain,
% 0.76/0.94      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94          = (k2_struct_0 @ sk_B))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['39', '40'])).
% 0.76/0.94  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('43', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_struct_0 @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.94  thf('44', plain,
% 0.76/0.94      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94          = (k2_funct_1 @ sk_C))
% 0.76/0.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.76/0.94      inference('demod', [status(thm)], ['31', '32', '37', '38', '43'])).
% 0.76/0.94  thf('45', plain,
% 0.76/0.94      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_funct_1 @ sk_C))),
% 0.76/0.94      inference('simplify', [status(thm)], ['44'])).
% 0.76/0.94  thf('46', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('47', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('48', plain,
% 0.76/0.94      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          != (k2_struct_0 @ sk_B))
% 0.76/0.94        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94            != (k2_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('49', plain,
% 0.76/0.94      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          != (k2_struct_0 @ sk_A)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('split', [status(esa)], ['48'])).
% 0.76/0.94  thf('50', plain,
% 0.76/0.94      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94           != (k2_struct_0 @ sk_A))
% 0.76/0.94         | ~ (l1_struct_0 @ sk_A)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['47', '49'])).
% 0.76/0.94  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('52', plain,
% 0.76/0.94      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          != (k2_struct_0 @ sk_A)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('demod', [status(thm)], ['50', '51'])).
% 0.76/0.94  thf('53', plain,
% 0.76/0.94      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94           != (k2_struct_0 @ sk_A))
% 0.76/0.94         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['46', '52'])).
% 0.76/0.94  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('55', plain,
% 0.76/0.94      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          != (k2_struct_0 @ sk_A)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.94  thf('56', plain,
% 0.76/0.94      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['45', '55'])).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(t24_relset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.94       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.76/0.94           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.76/0.94         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.76/0.94           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.94         (((k2_relset_1 @ X8 @ X7 @ (k3_relset_1 @ X7 @ X8 @ X9))
% 0.76/0.94            = (k1_relset_1 @ X7 @ X8 @ X9))
% 0.76/0.94          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.76/0.94      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.94  thf('61', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(redefinition_k3_relset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.94       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.94         (((k3_relset_1 @ X5 @ X6 @ X4) = (k4_relat_1 @ X4))
% 0.76/0.94          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.76/0.94      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k4_relat_1 @ sk_C))),
% 0.76/0.94      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/0.94  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(d9_funct_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.94       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.76/0.94  thf('65', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (v2_funct_1 @ X0)
% 0.76/0.94          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.76/0.94          | ~ (v1_funct_1 @ X0)
% 0.76/0.94          | ~ (v1_relat_1 @ X0))),
% 0.76/0.94      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.76/0.94  thf('66', plain,
% 0.76/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.94        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['64', '65'])).
% 0.76/0.94  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.76/0.94      inference('demod', [status(thm)], ['66', '67'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(cc1_relset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.94       ( v1_relat_1 @ C ) ))).
% 0.76/0.94  thf('70', plain,
% 0.76/0.94      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         ((v1_relat_1 @ X1)
% 0.76/0.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.76/0.94      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.94  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.94  thf('72', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['68', '71'])).
% 0.76/0.94  thf('73', plain,
% 0.76/0.94      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_funct_1 @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['63', '72'])).
% 0.76/0.94  thf('74', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['60', '73'])).
% 0.76/0.94  thf('75', plain,
% 0.76/0.94      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_funct_1 @ sk_C))
% 0.76/0.94          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['57', '74'])).
% 0.76/0.94  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('77', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['75', '76'])).
% 0.76/0.94  thf('78', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('79', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('80', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['60', '73'])).
% 0.76/0.94  thf('81', plain,
% 0.76/0.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_funct_1 @ sk_C))
% 0.76/0.94          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['79', '80'])).
% 0.76/0.94  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('83', plain,
% 0.76/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['81', '82'])).
% 0.76/0.94  thf('84', plain,
% 0.76/0.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_funct_1 @ sk_C))
% 0.76/0.94          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['78', '83'])).
% 0.76/0.94  thf('85', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('86', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('87', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('88', plain,
% 0.76/0.94      (((m1_subset_1 @ sk_C @ 
% 0.76/0.94         (k1_zfmisc_1 @ 
% 0.76/0.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['86', '87'])).
% 0.76/0.94  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('90', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['88', '89'])).
% 0.76/0.94  thf('91', plain,
% 0.76/0.94      (((m1_subset_1 @ sk_C @ 
% 0.76/0.94         (k1_zfmisc_1 @ 
% 0.76/0.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup+', [status(thm)], ['85', '90'])).
% 0.76/0.94  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('93', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['91', '92'])).
% 0.76/0.94  thf('94', plain,
% 0.76/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.94         (((k2_relset_1 @ X8 @ X7 @ (k3_relset_1 @ X7 @ X8 @ X9))
% 0.76/0.94            = (k1_relset_1 @ X7 @ X8 @ X9))
% 0.76/0.94          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.76/0.94      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.76/0.94  thf('95', plain,
% 0.76/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('sup-', [status(thm)], ['93', '94'])).
% 0.76/0.94  thf('96', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['91', '92'])).
% 0.76/0.94  thf('97', plain,
% 0.76/0.94      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.94         (((k3_relset_1 @ X5 @ X6 @ X4) = (k4_relat_1 @ X4))
% 0.76/0.94          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.76/0.94      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.76/0.94  thf('98', plain,
% 0.76/0.94      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k4_relat_1 @ sk_C))),
% 0.76/0.94      inference('sup-', [status(thm)], ['96', '97'])).
% 0.76/0.94  thf('99', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['68', '71'])).
% 0.76/0.94  thf('100', plain,
% 0.76/0.94      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_funct_1 @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['98', '99'])).
% 0.76/0.94  thf('101', plain,
% 0.76/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['95', '100'])).
% 0.76/0.94  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('103', plain,
% 0.76/0.94      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['84', '101', '102'])).
% 0.76/0.94  thf('104', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C))
% 0.76/0.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['77', '103'])).
% 0.76/0.94  thf('105', plain,
% 0.76/0.94      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94          != (k2_struct_0 @ sk_A)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_A))))),
% 0.76/0.94      inference('demod', [status(thm)], ['56', '104'])).
% 0.76/0.94  thf('106', plain,
% 0.76/0.94      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_funct_1 @ sk_C))),
% 0.76/0.94      inference('simplify', [status(thm)], ['44'])).
% 0.76/0.94  thf('107', plain,
% 0.76/0.94      (![X18 : $i]:
% 0.76/0.94         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.76/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.94  thf('108', plain,
% 0.76/0.94      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          != (k2_struct_0 @ sk_B)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('split', [status(esa)], ['48'])).
% 0.76/0.94  thf('109', plain,
% 0.76/0.94      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94           != (k2_struct_0 @ sk_B))
% 0.76/0.94         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['107', '108'])).
% 0.76/0.94  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('111', plain,
% 0.76/0.94      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          != (k2_struct_0 @ sk_B)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['109', '110'])).
% 0.76/0.94  thf('112', plain,
% 0.76/0.94      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['106', '111'])).
% 0.76/0.94  thf('113', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_C @ 
% 0.76/0.94        (k1_zfmisc_1 @ 
% 0.76/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('114', plain,
% 0.76/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.94         (((k1_relset_1 @ X8 @ X7 @ (k3_relset_1 @ X7 @ X8 @ X9))
% 0.76/0.94            = (k2_relset_1 @ X7 @ X8 @ X9))
% 0.76/0.94          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.76/0.94      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.76/0.94  thf('115', plain,
% 0.76/0.94      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94         = (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.76/0.94      inference('sup-', [status(thm)], ['113', '114'])).
% 0.76/0.94  thf('116', plain,
% 0.76/0.94      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_funct_1 @ sk_C))),
% 0.76/0.94      inference('demod', [status(thm)], ['63', '72'])).
% 0.76/0.94  thf('117', plain,
% 0.76/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         = (k2_struct_0 @ sk_B))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('118', plain,
% 0.76/0.94      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.76/0.94  thf('119', plain,
% 0.76/0.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.76/0.94         <= (~
% 0.76/0.94             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94                = (k2_struct_0 @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['112', '118'])).
% 0.76/0.94  thf('120', plain,
% 0.76/0.94      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          = (k2_struct_0 @ sk_B)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['119'])).
% 0.76/0.94  thf('121', plain,
% 0.76/0.94      (~
% 0.76/0.94       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          = (k2_struct_0 @ sk_A))) | 
% 0.76/0.94       ~
% 0.76/0.94       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          = (k2_struct_0 @ sk_B)))),
% 0.76/0.94      inference('split', [status(esa)], ['48'])).
% 0.76/0.94  thf('122', plain,
% 0.76/0.94      (~
% 0.76/0.94       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.94          = (k2_struct_0 @ sk_A)))),
% 0.76/0.94      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 0.76/0.94  thf('123', plain,
% 0.76/0.94      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.94         != (k2_struct_0 @ sk_A))),
% 0.76/0.94      inference('simpl_trail', [status(thm)], ['105', '122'])).
% 0.76/0.94  thf('124', plain,
% 0.76/0.94      (~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['24', '123'])).
% 0.76/0.94  thf('125', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['13', '124'])).
% 0.76/0.94  thf(fc2_struct_0, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.94       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.94  thf('126', plain,
% 0.76/0.94      (![X19 : $i]:
% 0.76/0.94         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.76/0.94          | ~ (l1_struct_0 @ X19)
% 0.76/0.94          | (v2_struct_0 @ X19))),
% 0.76/0.94      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.76/0.94  thf('127', plain,
% 0.76/0.94      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94        | (v2_struct_0 @ sk_B)
% 0.76/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.94      inference('sup-', [status(thm)], ['125', '126'])).
% 0.76/0.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.94  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('129', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('130', plain, ((v2_struct_0 @ sk_B)),
% 0.76/0.94      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.76/0.94  thf('131', plain, ($false), inference('demod', [status(thm)], ['0', '130'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
