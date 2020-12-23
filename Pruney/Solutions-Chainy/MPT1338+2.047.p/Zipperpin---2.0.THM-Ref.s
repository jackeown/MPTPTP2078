%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dirImPYO7k

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:55 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 384 expanded)
%              Number of leaves         :   39 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          : 1628 (9537 expanded)
%              Number of equality atoms :  115 ( 528 expanded)
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

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X7 @ ( k3_relset_1 @ X7 @ X8 @ X9 ) )
        = ( k1_relset_1 @ X7 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('89',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_relset_1 @ X5 @ X6 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('90',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('92',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['84','93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','95'])).

thf('97',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','96'])).

thf('98',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('99',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('101',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X7 @ ( k3_relset_1 @ X7 @ X8 @ X9 ) )
        = ( k2_relset_1 @ X7 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('107',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','72'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','110'])).

thf('112',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('114',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['97','114'])).

thf('116',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','115'])).

thf('117',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','116'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('118',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dirImPYO7k
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:30:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.92  % Solved by: fo/fo7.sh
% 0.68/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.92  % done 367 iterations in 0.469s
% 0.68/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.92  % SZS output start Refutation
% 0.68/0.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.68/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.68/0.92  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.68/0.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.68/0.92  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.68/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.92  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.68/0.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.68/0.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.68/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.92  thf(t62_tops_2, conjecture,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( l1_struct_0 @ A ) =>
% 0.68/0.92       ( ![B:$i]:
% 0.68/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.68/0.92           ( ![C:$i]:
% 0.68/0.92             ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.92                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.92                 ( m1_subset_1 @
% 0.68/0.92                   C @ 
% 0.68/0.92                   ( k1_zfmisc_1 @
% 0.68/0.92                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.92               ( ( ( ( k2_relset_1 @
% 0.68/0.92                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.68/0.93                     ( k2_struct_0 @ B ) ) & 
% 0.68/0.93                   ( v2_funct_1 @ C ) ) =>
% 0.68/0.93                 ( ( ( k1_relset_1 @
% 0.68/0.93                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.93                       ( k2_tops_2 @
% 0.68/0.93                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.93                     ( k2_struct_0 @ B ) ) & 
% 0.68/0.93                   ( ( k2_relset_1 @
% 0.68/0.93                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.93                       ( k2_tops_2 @
% 0.68/0.93                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.93                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.68/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.93    (~( ![A:$i]:
% 0.68/0.93        ( ( l1_struct_0 @ A ) =>
% 0.68/0.93          ( ![B:$i]:
% 0.68/0.93            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.68/0.93              ( ![C:$i]:
% 0.68/0.93                ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.93                    ( v1_funct_2 @
% 0.68/0.93                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.93                    ( m1_subset_1 @
% 0.68/0.93                      C @ 
% 0.68/0.93                      ( k1_zfmisc_1 @
% 0.68/0.93                        ( k2_zfmisc_1 @
% 0.68/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.93                  ( ( ( ( k2_relset_1 @
% 0.68/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.68/0.93                        ( k2_struct_0 @ B ) ) & 
% 0.68/0.93                      ( v2_funct_1 @ C ) ) =>
% 0.68/0.93                    ( ( ( k1_relset_1 @
% 0.68/0.93                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.93                          ( k2_tops_2 @
% 0.68/0.93                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.93                        ( k2_struct_0 @ B ) ) & 
% 0.68/0.93                      ( ( k2_relset_1 @
% 0.68/0.93                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.93                          ( k2_tops_2 @
% 0.68/0.93                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.93                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.68/0.93    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.68/0.93  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf(d1_funct_2, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i]:
% 0.68/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.68/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.68/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.68/0.93  thf(zf_stmt_1, axiom,
% 0.68/0.93    (![B:$i,A:$i]:
% 0.68/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.68/0.93  thf('1', plain,
% 0.68/0.93      (![X10 : $i, X11 : $i]:
% 0.68/0.93         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.93  thf(d3_struct_0, axiom,
% 0.68/0.93    (![A:$i]:
% 0.68/0.93     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.68/0.93  thf('2', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('3', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('4', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('5', plain,
% 0.68/0.93      (((m1_subset_1 @ sk_C @ 
% 0.68/0.93         (k1_zfmisc_1 @ 
% 0.68/0.93          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.93      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.93  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('7', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['5', '6'])).
% 0.68/0.93  thf('8', plain,
% 0.68/0.93      (((m1_subset_1 @ sk_C @ 
% 0.68/0.93         (k1_zfmisc_1 @ 
% 0.68/0.93          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup+', [status(thm)], ['2', '7'])).
% 0.68/0.93  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('10', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.93  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.68/0.93  thf(zf_stmt_3, axiom,
% 0.68/0.93    (![C:$i,B:$i,A:$i]:
% 0.68/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.68/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.68/0.93  thf(zf_stmt_5, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i]:
% 0.68/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.68/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.68/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.68/0.93  thf('11', plain,
% 0.68/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.93         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.68/0.93          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.68/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.93  thf('12', plain,
% 0.68/0.93      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.68/0.93        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.93  thf('13', plain,
% 0.68/0.93      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.68/0.93        | (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['1', '12'])).
% 0.68/0.93  thf('14', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('15', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('16', plain,
% 0.68/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('17', plain,
% 0.68/0.93      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.93      inference('sup+', [status(thm)], ['15', '16'])).
% 0.68/0.93  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('19', plain,
% 0.68/0.93      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.68/0.93      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.93  thf('20', plain,
% 0.68/0.93      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup+', [status(thm)], ['14', '19'])).
% 0.68/0.93  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('22', plain,
% 0.68/0.93      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.68/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.68/0.93  thf('23', plain,
% 0.68/0.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.93         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.68/0.93          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.68/0.93          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.93  thf('24', plain,
% 0.68/0.93      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.68/0.93        | ((k2_struct_0 @ sk_A)
% 0.68/0.93            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.93  thf('25', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('26', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('27', plain,
% 0.68/0.93      (((m1_subset_1 @ sk_C @ 
% 0.68/0.93         (k1_zfmisc_1 @ 
% 0.68/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup+', [status(thm)], ['25', '26'])).
% 0.68/0.93  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('29', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['27', '28'])).
% 0.68/0.93  thf(d4_tops_2, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i]:
% 0.68/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.68/0.93         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.68/0.93  thf('30', plain,
% 0.68/0.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.93         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.68/0.93          | ~ (v2_funct_1 @ X22)
% 0.68/0.93          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.68/0.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.68/0.93          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.68/0.93          | ~ (v1_funct_1 @ X22))),
% 0.68/0.93      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.68/0.93  thf('31', plain,
% 0.68/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.68/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.68/0.93        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93            = (k2_funct_1 @ sk_C))
% 0.68/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.68/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93            != (k2_struct_0 @ sk_B)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.93  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('33', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('34', plain,
% 0.68/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('35', plain,
% 0.68/0.93      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup+', [status(thm)], ['33', '34'])).
% 0.68/0.93  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('37', plain,
% 0.68/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.68/0.93      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.93  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('39', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('40', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_struct_0 @ sk_B))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('41', plain,
% 0.68/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93          = (k2_struct_0 @ sk_B))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup+', [status(thm)], ['39', '40'])).
% 0.68/0.93  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('43', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_struct_0 @ sk_B))),
% 0.68/0.93      inference('demod', [status(thm)], ['41', '42'])).
% 0.68/0.93  thf('44', plain,
% 0.68/0.93      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93          = (k2_funct_1 @ sk_C))
% 0.68/0.93        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.68/0.93      inference('demod', [status(thm)], ['31', '32', '37', '38', '43'])).
% 0.68/0.93  thf('45', plain,
% 0.68/0.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_funct_1 @ sk_C))),
% 0.68/0.93      inference('simplify', [status(thm)], ['44'])).
% 0.68/0.93  thf('46', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('47', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('48', plain,
% 0.68/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          != (k2_struct_0 @ sk_B))
% 0.68/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93            != (k2_struct_0 @ sk_A)))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('49', plain,
% 0.68/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          != (k2_struct_0 @ sk_A)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('split', [status(esa)], ['48'])).
% 0.68/0.93  thf('50', plain,
% 0.68/0.93      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93           != (k2_struct_0 @ sk_A))
% 0.68/0.93         | ~ (l1_struct_0 @ sk_A)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['47', '49'])).
% 0.68/0.93  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('52', plain,
% 0.68/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          != (k2_struct_0 @ sk_A)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('demod', [status(thm)], ['50', '51'])).
% 0.68/0.93  thf('53', plain,
% 0.68/0.93      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93           != (k2_struct_0 @ sk_A))
% 0.68/0.93         | ~ (l1_struct_0 @ sk_B)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['46', '52'])).
% 0.68/0.93  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('55', plain,
% 0.68/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          != (k2_struct_0 @ sk_A)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.93  thf('56', plain,
% 0.68/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['45', '55'])).
% 0.68/0.93  thf('57', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('58', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf(t24_relset_1, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i]:
% 0.68/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.93       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.68/0.93           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.68/0.93         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.68/0.93           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.93  thf('59', plain,
% 0.68/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.93         (((k2_relset_1 @ X8 @ X7 @ (k3_relset_1 @ X7 @ X8 @ X9))
% 0.68/0.93            = (k1_relset_1 @ X7 @ X8 @ X9))
% 0.68/0.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.68/0.93      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.68/0.93  thf('60', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.93  thf('61', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf(redefinition_k3_relset_1, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i]:
% 0.68/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.93       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.68/0.93  thf('62', plain,
% 0.68/0.93      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.93         (((k3_relset_1 @ X5 @ X6 @ X4) = (k4_relat_1 @ X4))
% 0.68/0.93          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.68/0.93      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.68/0.93  thf('63', plain,
% 0.68/0.93      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k4_relat_1 @ sk_C))),
% 0.68/0.93      inference('sup-', [status(thm)], ['61', '62'])).
% 0.68/0.93  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf(d9_funct_1, axiom,
% 0.68/0.93    (![A:$i]:
% 0.68/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.93       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.68/0.93  thf('65', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (~ (v2_funct_1 @ X0)
% 0.68/0.93          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.68/0.93          | ~ (v1_funct_1 @ X0)
% 0.68/0.93          | ~ (v1_relat_1 @ X0))),
% 0.68/0.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.68/0.93  thf('66', plain,
% 0.68/0.93      ((~ (v1_relat_1 @ sk_C)
% 0.68/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.68/0.93        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['64', '65'])).
% 0.68/0.93  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('68', plain,
% 0.68/0.93      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.68/0.93      inference('demod', [status(thm)], ['66', '67'])).
% 0.68/0.93  thf('69', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf(cc1_relset_1, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i]:
% 0.68/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.93       ( v1_relat_1 @ C ) ))).
% 0.68/0.93  thf('70', plain,
% 0.68/0.93      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.93         ((v1_relat_1 @ X1)
% 0.68/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.68/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.68/0.93  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.93      inference('sup-', [status(thm)], ['69', '70'])).
% 0.68/0.93  thf('72', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['68', '71'])).
% 0.68/0.93  thf('73', plain,
% 0.68/0.93      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_funct_1 @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['63', '72'])).
% 0.68/0.93  thf('74', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['60', '73'])).
% 0.68/0.93  thf('75', plain,
% 0.68/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_funct_1 @ sk_C))
% 0.68/0.93          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.93      inference('sup+', [status(thm)], ['57', '74'])).
% 0.68/0.93  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('77', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['75', '76'])).
% 0.68/0.93  thf('78', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('79', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('80', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['60', '73'])).
% 0.68/0.93  thf('81', plain,
% 0.68/0.93      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_funct_1 @ sk_C))
% 0.68/0.93          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup+', [status(thm)], ['79', '80'])).
% 0.68/0.93  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('83', plain,
% 0.68/0.93      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['81', '82'])).
% 0.68/0.93  thf('84', plain,
% 0.68/0.93      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_funct_1 @ sk_C))
% 0.68/0.93          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.93      inference('sup+', [status(thm)], ['78', '83'])).
% 0.68/0.93  thf('85', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.93  thf('86', plain,
% 0.68/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.93         (((k2_relset_1 @ X8 @ X7 @ (k3_relset_1 @ X7 @ X8 @ X9))
% 0.68/0.93            = (k1_relset_1 @ X7 @ X8 @ X9))
% 0.68/0.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.68/0.93      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.68/0.93  thf('87', plain,
% 0.68/0.93      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('sup-', [status(thm)], ['85', '86'])).
% 0.68/0.93  thf('88', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.93  thf('89', plain,
% 0.68/0.93      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.93         (((k3_relset_1 @ X5 @ X6 @ X4) = (k4_relat_1 @ X4))
% 0.68/0.93          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.68/0.93      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.68/0.93  thf('90', plain,
% 0.68/0.93      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k4_relat_1 @ sk_C))),
% 0.68/0.93      inference('sup-', [status(thm)], ['88', '89'])).
% 0.68/0.93  thf('91', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['68', '71'])).
% 0.68/0.93  thf('92', plain,
% 0.68/0.93      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_funct_1 @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['90', '91'])).
% 0.68/0.93  thf('93', plain,
% 0.68/0.93      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['87', '92'])).
% 0.68/0.93  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('95', plain,
% 0.68/0.93      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['84', '93', '94'])).
% 0.68/0.93  thf('96', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C))
% 0.68/0.93         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['77', '95'])).
% 0.68/0.93  thf('97', plain,
% 0.68/0.93      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93          != (k2_struct_0 @ sk_A)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_A))))),
% 0.68/0.93      inference('demod', [status(thm)], ['56', '96'])).
% 0.68/0.93  thf('98', plain,
% 0.68/0.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_funct_1 @ sk_C))),
% 0.68/0.93      inference('simplify', [status(thm)], ['44'])).
% 0.68/0.93  thf('99', plain,
% 0.68/0.93      (![X18 : $i]:
% 0.68/0.93         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.68/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.93  thf('100', plain,
% 0.68/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          != (k2_struct_0 @ sk_B)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('split', [status(esa)], ['48'])).
% 0.68/0.93  thf('101', plain,
% 0.68/0.93      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93           != (k2_struct_0 @ sk_B))
% 0.68/0.93         | ~ (l1_struct_0 @ sk_B)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['99', '100'])).
% 0.68/0.93  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('103', plain,
% 0.68/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          != (k2_struct_0 @ sk_B)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['101', '102'])).
% 0.68/0.93  thf('104', plain,
% 0.68/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['98', '103'])).
% 0.68/0.93  thf('105', plain,
% 0.68/0.93      ((m1_subset_1 @ sk_C @ 
% 0.68/0.93        (k1_zfmisc_1 @ 
% 0.68/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('106', plain,
% 0.68/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.93         (((k1_relset_1 @ X8 @ X7 @ (k3_relset_1 @ X7 @ X8 @ X9))
% 0.68/0.93            = (k2_relset_1 @ X7 @ X8 @ X9))
% 0.68/0.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.68/0.93      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.68/0.93  thf('107', plain,
% 0.68/0.93      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93         = (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.68/0.93      inference('sup-', [status(thm)], ['105', '106'])).
% 0.68/0.93  thf('108', plain,
% 0.68/0.93      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_funct_1 @ sk_C))),
% 0.68/0.93      inference('demod', [status(thm)], ['63', '72'])).
% 0.68/0.93  thf('109', plain,
% 0.68/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         = (k2_struct_0 @ sk_B))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('110', plain,
% 0.68/0.93      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.68/0.93      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.68/0.93  thf('111', plain,
% 0.68/0.93      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.68/0.93         <= (~
% 0.68/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93                = (k2_struct_0 @ sk_B))))),
% 0.68/0.93      inference('demod', [status(thm)], ['104', '110'])).
% 0.68/0.93  thf('112', plain,
% 0.68/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          = (k2_struct_0 @ sk_B)))),
% 0.68/0.93      inference('simplify', [status(thm)], ['111'])).
% 0.68/0.93  thf('113', plain,
% 0.68/0.93      (~
% 0.68/0.93       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          = (k2_struct_0 @ sk_A))) | 
% 0.68/0.93       ~
% 0.68/0.93       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          = (k2_struct_0 @ sk_B)))),
% 0.68/0.93      inference('split', [status(esa)], ['48'])).
% 0.68/0.93  thf('114', plain,
% 0.68/0.93      (~
% 0.68/0.93       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.93          = (k2_struct_0 @ sk_A)))),
% 0.68/0.93      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 0.68/0.93  thf('115', plain,
% 0.68/0.93      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.93         != (k2_struct_0 @ sk_A))),
% 0.68/0.93      inference('simpl_trail', [status(thm)], ['97', '114'])).
% 0.68/0.93  thf('116', plain,
% 0.68/0.93      (~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.68/0.93      inference('simplify_reflect-', [status(thm)], ['24', '115'])).
% 0.68/0.93  thf('117', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.68/0.93      inference('sup-', [status(thm)], ['13', '116'])).
% 0.68/0.93  thf(fc5_struct_0, axiom,
% 0.68/0.93    (![A:$i]:
% 0.68/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.93       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.68/0.93  thf('118', plain,
% 0.68/0.93      (![X19 : $i]:
% 0.68/0.93         (~ (v1_xboole_0 @ (k2_struct_0 @ X19))
% 0.68/0.93          | ~ (l1_struct_0 @ X19)
% 0.68/0.93          | (v2_struct_0 @ X19))),
% 0.68/0.93      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.68/0.93  thf('119', plain,
% 0.68/0.93      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.68/0.93        | (v2_struct_0 @ sk_B)
% 0.68/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.93      inference('sup-', [status(thm)], ['117', '118'])).
% 0.68/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.68/0.93  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.68/0.93  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('122', plain, ((v2_struct_0 @ sk_B)),
% 0.68/0.93      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.68/0.93  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.68/0.93  
% 0.68/0.93  % SZS output end Refutation
% 0.68/0.93  
% 0.78/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
