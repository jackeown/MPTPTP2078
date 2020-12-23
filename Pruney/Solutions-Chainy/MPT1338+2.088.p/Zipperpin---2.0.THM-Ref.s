%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HDYaPDp9Jx

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:02 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 489 expanded)
%              Number of leaves         :   40 ( 160 expanded)
%              Depth                    :   24
%              Number of atoms          : 1796 (11927 expanded)
%              Number of equality atoms :  128 ( 653 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X8 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) )
        = ( k1_relset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k3_relset_1 @ X6 @ X7 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('62',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('75',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X8 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) )
        = ( k1_relset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k3_relset_1 @ X6 @ X7 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('82',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('84',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X8 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) )
        = ( k1_relset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('97',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k3_relset_1 @ X6 @ X7 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('98',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('100',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','101'])).

thf('103',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('108',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['105','110'])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['74','111'])).

thf('113',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','112'])).

thf('114',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('115',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('117',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X8 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) )
        = ( k2_relset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('123',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','126'])).

thf('128',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('130',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['128','129'])).

thf('131',plain,(
    ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['113','130'])).

thf('132',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','131'])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','132'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('134',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('135',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('136',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('137',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HDYaPDp9Jx
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 420 iterations in 0.542s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.77/0.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.77/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.77/0.99  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.77/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.77/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.77/0.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.77/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.99  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.77/0.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.77/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.99  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.77/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.77/0.99  thf(t62_tops_2, conjecture,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( l1_struct_0 @ A ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.77/0.99           ( ![C:$i]:
% 0.77/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.77/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.77/0.99                 ( m1_subset_1 @
% 0.77/0.99                   C @ 
% 0.77/0.99                   ( k1_zfmisc_1 @
% 0.77/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.99               ( ( ( ( k2_relset_1 @
% 0.77/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.77/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.77/0.99                   ( v2_funct_1 @ C ) ) =>
% 0.77/0.99                 ( ( ( k1_relset_1 @
% 0.77/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.77/0.99                       ( k2_tops_2 @
% 0.77/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.77/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.77/0.99                   ( ( k2_relset_1 @
% 0.77/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.77/0.99                       ( k2_tops_2 @
% 0.77/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.77/0.99                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i]:
% 0.77/0.99        ( ( l1_struct_0 @ A ) =>
% 0.77/0.99          ( ![B:$i]:
% 0.77/0.99            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.77/0.99              ( ![C:$i]:
% 0.77/0.99                ( ( ( v1_funct_1 @ C ) & 
% 0.77/0.99                    ( v1_funct_2 @
% 0.77/0.99                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.77/0.99                    ( m1_subset_1 @
% 0.77/0.99                      C @ 
% 0.77/0.99                      ( k1_zfmisc_1 @
% 0.77/0.99                        ( k2_zfmisc_1 @
% 0.77/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.99                  ( ( ( ( k2_relset_1 @
% 0.77/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.77/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.77/0.99                      ( v2_funct_1 @ C ) ) =>
% 0.77/0.99                    ( ( ( k1_relset_1 @
% 0.77/0.99                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.77/0.99                          ( k2_tops_2 @
% 0.77/0.99                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.77/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.77/0.99                      ( ( k2_relset_1 @
% 0.77/0.99                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.77/0.99                          ( k2_tops_2 @
% 0.77/0.99                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.77/0.99                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.77/0.99  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(d3_struct_0, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('2', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf(d1_funct_2, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.77/0.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.77/0.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.77/0.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_1, axiom,
% 0.77/0.99    (![B:$i,A:$i]:
% 0.77/0.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.99       ( zip_tseitin_0 @ B @ A ) ))).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (![X11 : $i, X12 : $i]:
% 0.77/0.99         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.99  thf('4', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.77/0.99  thf(zf_stmt_3, axiom,
% 0.77/0.99    (![C:$i,B:$i,A:$i]:
% 0.77/0.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.77/0.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.77/0.99  thf(zf_stmt_5, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.77/0.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.77/0.99         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.77/0.99          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.77/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.99  thf('6', plain,
% 0.77/0.99      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.99        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.99  thf('7', plain,
% 0.77/0.99      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.77/0.99        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '6'])).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_B)
% 0.77/0.99        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['2', '7'])).
% 0.77/0.99  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('10', plain,
% 0.77/0.99      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.99        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['8', '9'])).
% 0.77/0.99  thf('11', plain,
% 0.77/0.99      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_A)
% 0.77/0.99        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['1', '10'])).
% 0.77/0.99  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('13', plain,
% 0.77/0.99      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.77/0.99        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.99  thf('14', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('15', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('16', plain,
% 0.77/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('17', plain,
% 0.77/0.99      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.77/0.99      inference('sup+', [status(thm)], ['15', '16'])).
% 0.77/0.99  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('19', plain,
% 0.77/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['17', '18'])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['14', '19'])).
% 0.77/0.99  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('22', plain,
% 0.77/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['20', '21'])).
% 0.77/0.99  thf('23', plain,
% 0.77/0.99      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.99         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.77/0.99          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.77/0.99          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.99  thf('24', plain,
% 0.77/0.99      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.77/0.99        | ((k2_struct_0 @ sk_A)
% 0.77/0.99            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/0.99  thf('25', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('26', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      (((m1_subset_1 @ sk_C @ 
% 0.77/0.99         (k1_zfmisc_1 @ 
% 0.77/0.99          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['25', '26'])).
% 0.77/0.99  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('29', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf(d4_tops_2, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.99       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.77/0.99         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.77/0.99  thf('30', plain,
% 0.77/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.99         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.77/0.99          | ~ (v2_funct_1 @ X23)
% 0.77/0.99          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.77/0.99          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.77/0.99          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.77/0.99          | ~ (v1_funct_1 @ X23))),
% 0.77/0.99      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.77/0.99  thf('31', plain,
% 0.77/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.77/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.77/0.99        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99            = (k2_funct_1 @ sk_C))
% 0.77/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.77/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99            != (k2_struct_0 @ sk_B)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.99  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('33', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('34', plain,
% 0.77/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('35', plain,
% 0.77/0.99      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/0.99  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('37', plain,
% 0.77/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['35', '36'])).
% 0.77/0.99  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('39', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('40', plain,
% 0.77/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k2_struct_0 @ sk_B))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('41', plain,
% 0.77/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99          = (k2_struct_0 @ sk_B))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['39', '40'])).
% 0.77/0.99  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('43', plain,
% 0.77/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k2_struct_0 @ sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['41', '42'])).
% 0.77/0.99  thf('44', plain,
% 0.77/0.99      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99          = (k2_funct_1 @ sk_C))
% 0.77/0.99        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.77/0.99      inference('demod', [status(thm)], ['31', '32', '37', '38', '43'])).
% 0.77/0.99  thf('45', plain,
% 0.77/0.99      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k2_funct_1 @ sk_C))),
% 0.77/0.99      inference('simplify', [status(thm)], ['44'])).
% 0.77/0.99  thf('46', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('47', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('48', plain,
% 0.77/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99          != (k2_struct_0 @ sk_B))
% 0.77/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99            != (k2_struct_0 @ sk_A)))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('49', plain,
% 0.77/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99          != (k2_struct_0 @ sk_A)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99                = (k2_struct_0 @ sk_A))))),
% 0.77/0.99      inference('split', [status(esa)], ['48'])).
% 0.77/0.99  thf('50', plain,
% 0.77/0.99      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99           != (k2_struct_0 @ sk_A))
% 0.77/0.99         | ~ (l1_struct_0 @ sk_B)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99                = (k2_struct_0 @ sk_A))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['47', '49'])).
% 0.77/0.99  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('52', plain,
% 0.77/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99          != (k2_struct_0 @ sk_A)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99                = (k2_struct_0 @ sk_A))))),
% 0.77/0.99      inference('demod', [status(thm)], ['50', '51'])).
% 0.77/0.99  thf('53', plain,
% 0.77/0.99      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99           != (k2_struct_0 @ sk_A))
% 0.77/0.99         | ~ (l1_struct_0 @ sk_B)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99                = (k2_struct_0 @ sk_A))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['46', '52'])).
% 0.77/0.99  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('55', plain,
% 0.77/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99          != (k2_struct_0 @ sk_A)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99                = (k2_struct_0 @ sk_A))))),
% 0.77/0.99      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.99  thf('56', plain,
% 0.77/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.77/0.99         <= (~
% 0.77/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99                = (k2_struct_0 @ sk_A))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['45', '55'])).
% 0.77/0.99  thf('57', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf(t24_relset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.99       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.77/0.99           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.77/0.99         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.77/0.99           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.99  thf('58', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/0.99         (((k2_relset_1 @ X9 @ X8 @ (k3_relset_1 @ X8 @ X9 @ X10))
% 0.77/0.99            = (k1_relset_1 @ X8 @ X9 @ X10))
% 0.77/0.99          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.77/0.99      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.77/0.99  thf('59', plain,
% 0.77/0.99      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/0.99      inference('sup-', [status(thm)], ['57', '58'])).
% 0.77/0.99  thf('60', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf(redefinition_k3_relset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.99       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.77/0.99  thf('61', plain,
% 0.77/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.99         (((k3_relset_1 @ X6 @ X7 @ X5) = (k4_relat_1 @ X5))
% 0.77/0.99          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.77/0.99      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.77/0.99  thf('62', plain,
% 0.77/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k4_relat_1 @ sk_C))),
% 0.77/0.99      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.99  thf('63', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(cc2_relat_1, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( v1_relat_1 @ A ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.77/0.99  thf('64', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.77/0.99          | (v1_relat_1 @ X0)
% 0.77/0.99          | ~ (v1_relat_1 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.77/0.99  thf('65', plain,
% 0.77/0.99      ((~ (v1_relat_1 @ 
% 0.77/0.99           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.77/0.99        | (v1_relat_1 @ sk_C))),
% 0.77/0.99      inference('sup-', [status(thm)], ['63', '64'])).
% 0.77/0.99  thf(fc6_relat_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.77/0.99  thf('66', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.77/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/0.99  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.99      inference('demod', [status(thm)], ['65', '66'])).
% 0.77/0.99  thf(d9_funct_1, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.99       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.77/0.99  thf('68', plain,
% 0.77/0.99      (![X4 : $i]:
% 0.77/0.99         (~ (v2_funct_1 @ X4)
% 0.77/0.99          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.77/0.99          | ~ (v1_funct_1 @ X4)
% 0.77/0.99          | ~ (v1_relat_1 @ X4))),
% 0.77/0.99      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.77/0.99  thf('69', plain,
% 0.77/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.77/0.99        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.77/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.77/0.99      inference('sup-', [status(thm)], ['67', '68'])).
% 0.77/0.99  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('72', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.77/0.99  thf('73', plain,
% 0.77/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k2_funct_1 @ sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['62', '72'])).
% 0.77/0.99  thf('74', plain,
% 0.77/0.99      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99         (k2_funct_1 @ sk_C))
% 0.77/0.99         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['59', '73'])).
% 0.77/0.99  thf('75', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('76', plain,
% 0.77/0.99      (![X19 : $i]:
% 0.77/0.99         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.99  thf('77', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('78', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/0.99         (((k2_relset_1 @ X9 @ X8 @ (k3_relset_1 @ X8 @ X9 @ X10))
% 0.77/0.99            = (k1_relset_1 @ X8 @ X9 @ X10))
% 0.77/0.99          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.77/0.99      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.77/0.99  thf('79', plain,
% 0.77/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/0.99      inference('sup-', [status(thm)], ['77', '78'])).
% 0.77/0.99  thf('80', plain,
% 0.77/0.99      ((m1_subset_1 @ sk_C @ 
% 0.77/0.99        (k1_zfmisc_1 @ 
% 0.77/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('81', plain,
% 0.77/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.99         (((k3_relset_1 @ X6 @ X7 @ X5) = (k4_relat_1 @ X5))
% 0.77/0.99          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.77/0.99      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.77/0.99  thf('82', plain,
% 0.77/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k4_relat_1 @ sk_C))),
% 0.77/0.99      inference('sup-', [status(thm)], ['80', '81'])).
% 0.77/0.99  thf('83', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.77/0.99  thf('84', plain,
% 0.77/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.99         = (k2_funct_1 @ sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['82', '83'])).
% 0.77/0.99  thf('85', plain,
% 0.77/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.99         (k2_funct_1 @ sk_C))
% 0.77/0.99         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/0.99      inference('demod', [status(thm)], ['79', '84'])).
% 0.77/0.99  thf('86', plain,
% 0.77/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.77/0.99          (k2_funct_1 @ sk_C))
% 0.77/0.99          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.77/0.99      inference('sup+', [status(thm)], ['76', '85'])).
% 0.77/0.99  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('88', plain,
% 0.77/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.77/1.00         (k2_funct_1 @ sk_C))
% 0.77/1.00         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['86', '87'])).
% 0.77/1.00  thf('89', plain,
% 0.77/1.00      (![X19 : $i]:
% 0.77/1.00         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/1.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/1.00  thf('90', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_C @ 
% 0.77/1.00        (k1_zfmisc_1 @ 
% 0.77/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('91', plain,
% 0.77/1.00      (((m1_subset_1 @ sk_C @ 
% 0.77/1.00         (k1_zfmisc_1 @ 
% 0.77/1.00          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.77/1.00        | ~ (l1_struct_0 @ sk_A))),
% 0.77/1.00      inference('sup+', [status(thm)], ['89', '90'])).
% 0.77/1.00  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('93', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_C @ 
% 0.77/1.00        (k1_zfmisc_1 @ 
% 0.77/1.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/1.00      inference('demod', [status(thm)], ['91', '92'])).
% 0.77/1.00  thf('94', plain,
% 0.77/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/1.00         (((k2_relset_1 @ X9 @ X8 @ (k3_relset_1 @ X8 @ X9 @ X10))
% 0.77/1.00            = (k1_relset_1 @ X8 @ X9 @ X10))
% 0.77/1.00          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.77/1.00      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.77/1.00  thf('95', plain,
% 0.77/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.77/1.00         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('sup-', [status(thm)], ['93', '94'])).
% 0.77/1.00  thf('96', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_C @ 
% 0.77/1.00        (k1_zfmisc_1 @ 
% 0.77/1.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/1.00      inference('demod', [status(thm)], ['91', '92'])).
% 0.77/1.00  thf('97', plain,
% 0.77/1.00      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/1.00         (((k3_relset_1 @ X6 @ X7 @ X5) = (k4_relat_1 @ X5))
% 0.77/1.00          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.77/1.00      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.77/1.00  thf('98', plain,
% 0.77/1.00      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k4_relat_1 @ sk_C))),
% 0.77/1.00      inference('sup-', [status(thm)], ['96', '97'])).
% 0.77/1.00  thf('99', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.77/1.00  thf('100', plain,
% 0.77/1.00      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k2_funct_1 @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['98', '99'])).
% 0.77/1.00  thf('101', plain,
% 0.77/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.77/1.00         (k2_funct_1 @ sk_C))
% 0.77/1.00         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['95', '100'])).
% 0.77/1.00  thf('102', plain,
% 0.77/1.00      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['88', '101'])).
% 0.77/1.00  thf('103', plain,
% 0.77/1.00      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00        | ~ (l1_struct_0 @ sk_B))),
% 0.77/1.00      inference('sup+', [status(thm)], ['75', '102'])).
% 0.77/1.00  thf('104', plain, ((l1_struct_0 @ sk_B)),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('105', plain,
% 0.77/1.00      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['103', '104'])).
% 0.77/1.00  thf('106', plain,
% 0.77/1.00      (![X19 : $i]:
% 0.77/1.00         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/1.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/1.00  thf('107', plain,
% 0.77/1.00      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['103', '104'])).
% 0.77/1.00  thf('108', plain,
% 0.77/1.00      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00        | ~ (l1_struct_0 @ sk_A))),
% 0.77/1.00      inference('sup+', [status(thm)], ['106', '107'])).
% 0.77/1.00  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('110', plain,
% 0.77/1.00      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['108', '109'])).
% 0.77/1.00  thf('111', plain,
% 0.77/1.00      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['105', '110'])).
% 0.77/1.00  thf('112', plain,
% 0.77/1.00      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00         (k2_funct_1 @ sk_C))
% 0.77/1.00         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['74', '111'])).
% 0.77/1.00  thf('113', plain,
% 0.77/1.00      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00          != (k2_struct_0 @ sk_A)))
% 0.77/1.00         <= (~
% 0.77/1.00             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00                = (k2_struct_0 @ sk_A))))),
% 0.77/1.00      inference('demod', [status(thm)], ['56', '112'])).
% 0.77/1.00  thf('114', plain,
% 0.77/1.00      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k2_funct_1 @ sk_C))),
% 0.77/1.00      inference('simplify', [status(thm)], ['44'])).
% 0.77/1.00  thf('115', plain,
% 0.77/1.00      (![X19 : $i]:
% 0.77/1.00         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.77/1.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/1.00  thf('116', plain,
% 0.77/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00          != (k2_struct_0 @ sk_B)))
% 0.77/1.00         <= (~
% 0.77/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00                = (k2_struct_0 @ sk_B))))),
% 0.77/1.00      inference('split', [status(esa)], ['48'])).
% 0.77/1.00  thf('117', plain,
% 0.77/1.00      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00           != (k2_struct_0 @ sk_B))
% 0.77/1.00         | ~ (l1_struct_0 @ sk_B)))
% 0.77/1.00         <= (~
% 0.77/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00                = (k2_struct_0 @ sk_B))))),
% 0.77/1.00      inference('sup-', [status(thm)], ['115', '116'])).
% 0.77/1.00  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('119', plain,
% 0.77/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00          != (k2_struct_0 @ sk_B)))
% 0.77/1.00         <= (~
% 0.77/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00                = (k2_struct_0 @ sk_B))))),
% 0.77/1.00      inference('demod', [status(thm)], ['117', '118'])).
% 0.77/1.00  thf('120', plain,
% 0.77/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))
% 0.77/1.00         <= (~
% 0.77/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00                = (k2_struct_0 @ sk_B))))),
% 0.77/1.00      inference('sup-', [status(thm)], ['114', '119'])).
% 0.77/1.00  thf('121', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_C @ 
% 0.77/1.00        (k1_zfmisc_1 @ 
% 0.77/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('122', plain,
% 0.77/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/1.00         (((k1_relset_1 @ X9 @ X8 @ (k3_relset_1 @ X8 @ X9 @ X10))
% 0.77/1.00            = (k2_relset_1 @ X8 @ X9 @ X10))
% 0.77/1.00          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.77/1.00      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.77/1.00  thf('123', plain,
% 0.77/1.00      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00         = (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.77/1.00      inference('sup-', [status(thm)], ['121', '122'])).
% 0.77/1.00  thf('124', plain,
% 0.77/1.00      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k2_funct_1 @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['82', '83'])).
% 0.77/1.00  thf('125', plain,
% 0.77/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         = (k2_struct_0 @ sk_B))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('126', plain,
% 0.77/1.00      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.77/1.00      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.77/1.00  thf('127', plain,
% 0.77/1.00      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.77/1.00         <= (~
% 0.77/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00                = (k2_struct_0 @ sk_B))))),
% 0.77/1.00      inference('demod', [status(thm)], ['120', '126'])).
% 0.77/1.00  thf('128', plain,
% 0.77/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00          = (k2_struct_0 @ sk_B)))),
% 0.77/1.00      inference('simplify', [status(thm)], ['127'])).
% 0.77/1.00  thf('129', plain,
% 0.77/1.00      (~
% 0.77/1.00       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00          = (k2_struct_0 @ sk_A))) | 
% 0.77/1.00       ~
% 0.77/1.00       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00          = (k2_struct_0 @ sk_B)))),
% 0.77/1.00      inference('split', [status(esa)], ['48'])).
% 0.77/1.00  thf('130', plain,
% 0.77/1.00      (~
% 0.77/1.00       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/1.00          = (k2_struct_0 @ sk_A)))),
% 0.77/1.00      inference('sat_resolution*', [status(thm)], ['128', '129'])).
% 0.77/1.00  thf('131', plain,
% 0.77/1.00      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/1.00         != (k2_struct_0 @ sk_A))),
% 0.77/1.00      inference('simpl_trail', [status(thm)], ['113', '130'])).
% 0.77/1.00  thf('132', plain,
% 0.77/1.00      (~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['24', '131'])).
% 0.77/1.00  thf('133', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['13', '132'])).
% 0.77/1.00  thf(fc2_struct_0, axiom,
% 0.77/1.00    (![A:$i]:
% 0.77/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.77/1.00       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.77/1.00  thf('134', plain,
% 0.77/1.00      (![X20 : $i]:
% 0.77/1.00         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.77/1.00          | ~ (l1_struct_0 @ X20)
% 0.77/1.00          | (v2_struct_0 @ X20))),
% 0.77/1.00      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.77/1.00  thf('135', plain,
% 0.77/1.00      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.77/1.00        | (v2_struct_0 @ sk_B)
% 0.77/1.00        | ~ (l1_struct_0 @ sk_B))),
% 0.77/1.00      inference('sup-', [status(thm)], ['133', '134'])).
% 0.77/1.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/1.00  thf('136', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/1.00  thf('137', plain, ((l1_struct_0 @ sk_B)),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('138', plain, ((v2_struct_0 @ sk_B)),
% 0.77/1.00      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.77/1.00  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 0.77/1.00  
% 0.77/1.00  % SZS output end Refutation
% 0.77/1.00  
% 0.84/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
