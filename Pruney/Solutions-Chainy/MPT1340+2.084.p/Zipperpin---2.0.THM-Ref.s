%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4BSkZAXumu

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:21 EST 2020

% Result     : Theorem 46.64s
% Output     : Refutation 46.64s
% Verified   : 
% Statistics : Number of formulae       :  772 (357028 expanded)
%              Number of leaves         :   49 (101009 expanded)
%              Depth                    :   68
%              Number of atoms          : 8967 (7065813 expanded)
%              Number of equality atoms :  438 (198073 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
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
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

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
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','19','20','25'])).

thf('27',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('36',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('45',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50','53'])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('60',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('69',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('70',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('71',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('77',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('78',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['68','91'])).

thf('93',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('94',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('95',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('96',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('97',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('99',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('101',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('102',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('103',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('105',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('106',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('107',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('108',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('130',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('131',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('132',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('133',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('134',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('136',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('137',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('139',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('141',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != X21 )
      | ( v1_partfun1 @ X22 @ X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('142',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v4_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
      | ( v1_partfun1 @ X22 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['136','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['134','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('173',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('174',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('175',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('176',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('177',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('178',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('179',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('180',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('181',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['178','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['176','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['175','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['174','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['173','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['172','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('202',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('204',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('206',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('207',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('208',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('209',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['208','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['207','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('219',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('220',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('221',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['220','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['219','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['217','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['205','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['171','240'])).

thf('242',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('243',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('244',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('247',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('248',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['244','245','246','247','248'])).

thf('250',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('252',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('254',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('256',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('257',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('260',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('261',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['257','258','259','260','261'])).

thf('263',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['241','254','263'])).

thf('265',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','264'])).

thf('266',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('267',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['265','266','267','268'])).

thf('270',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('271',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','269','270','271','272'])).

thf('274',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','273'])).

thf('275',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','274'])).

thf('276',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('277',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_funct_2 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('278',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['276','278'])).

thf('280',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('284',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('287',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('288',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['34','286','287'])).

thf('289',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('290',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('291',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50','53'])).

thf('292',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['291','292'])).

thf('294',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50','53'])).

thf('295',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['294','295'])).

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

thf('297',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('298',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['296','298'])).

thf('300',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['293','299'])).

thf('301',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['290','301'])).

thf('303',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('305',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('306',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['304','305'])).

thf('307',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('308',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('309',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['308','309'])).

thf('311',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('314',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('317',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['316','317'])).

thf('319',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['314','315','320'])).

thf('322',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('323',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('325',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('326',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('327',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['323','324','327'])).

thf('329',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['328','329'])).

thf('331',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['307','330'])).

thf('332',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('334',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['323','324','327'])).

thf('335',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['334','335'])).

thf('337',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['333','336'])).

thf('338',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X29 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('340',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ k1_xboole_0 @ X27 )
      | ( v1_partfun1 @ X28 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['338','340'])).

thf('342',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['341','342'])).

thf('344',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['332','343'])).

thf('345',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('347',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('349',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['306','349'])).

thf('351',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['350'])).

thf('352',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('353',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('354',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('355',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('356',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('357',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('358',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('359',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('360',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['358','359'])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['357','360'])).

thf('362',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['356','362'])).

thf('364',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['355','364'])).

thf('366',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['354','366'])).

thf('368',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('370',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['368','369'])).

thf('371',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['353','370'])).

thf('372',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['352','371'])).

thf('373',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('374',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('375',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('376',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('377',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('378',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('379',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('380',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('381',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('382',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('383',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['381','382'])).

thf('384',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['380','383'])).

thf('385',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('386',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['379','385'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['378','387'])).

thf('389',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['377','388'])).

thf('390',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['376','390'])).

thf('392',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['391'])).

thf('393',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['375','392'])).

thf('394',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['393'])).

thf('395',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['374','394'])).

thf('396',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['395'])).

thf('397',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['373','396'])).

thf('398',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['397'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('400',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['367'])).

thf('401',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['399','400'])).

thf('402',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['401'])).

thf('403',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('404',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['402','403'])).

thf('405',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['398','404'])).

thf('406',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('408',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('409',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['406','409'])).

thf('411',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['410'])).

thf('412',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['351','411'])).

thf('413',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('414',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('415',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('416',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('417',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['412','413','414','415','416'])).

thf('418',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['417'])).

thf('419',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('420',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['350'])).

thf('421',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['405'])).

thf('422',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['420','421'])).

thf('423',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('424',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('425',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['422','423','424','425','426'])).

thf('428',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['427'])).

thf('429',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('430',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('431',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('432',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['430','431'])).

thf('433',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['429','432'])).

thf('434',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['433','434'])).

thf('436',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['428','435'])).

thf('437',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['419','436'])).

thf('438',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['437','438'])).

thf('440',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['418','439'])).

thf('441',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['440'])).

thf('442',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('443',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('444',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['442','443'])).

thf('445',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('446',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['444','445'])).

thf('447',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('448',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('449',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['447','448'])).

thf('450',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['446','449'])).

thf('451',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['441','450'])).

thf('452',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['451'])).

thf('453',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('454',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('455',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['453','454'])).

thf('456',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['455'])).

thf('457',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['452','456'])).

thf('458',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('459',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('460',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['458','459'])).

thf('461',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('462',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('463',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('464',plain,
    ( ( ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['457','460','461','462','463'])).

thf('465',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['446','449'])).

thf('466',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('467',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('468',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['466','467'])).

thf('469',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['465','468'])).

thf('470',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['464','469'])).

thf('471',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(simplify,[status(thm)],['470'])).

thf('472',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['289','471'])).

thf('473',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('474',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('475',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('478',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('479',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['288','477','478'])).

thf('480',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('481',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X38 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('482',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['480','481'])).

thf('483',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['262'])).

thf('484',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('485',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X30 ) @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('486',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['484','485'])).

thf('487',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('488',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('489',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('490',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('491',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['486','487','488','489','490'])).

thf('492',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['491'])).

thf('493',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['482','483','492'])).

thf('494',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('495',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('496',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('497',plain,(
    m1_subset_1 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['493','494','495','496'])).

thf('498',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('499',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['497','498'])).

thf('500',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('501',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X38 @ X39 @ X40 ) @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('502',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['500','501'])).

thf('503',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['262'])).

thf('504',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['491'])).

thf('505',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['502','503','504'])).

thf('506',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('507',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('508',plain,(
    v1_funct_2 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['505','506','507'])).

thf('509',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('510',plain,(
    v1_funct_2 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['508','509'])).

thf('511',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['499','510'])).

thf('512',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['288','477','478'])).

thf('513',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['511','512'])).

thf('514',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('515',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['277'])).

thf('516',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['514','515'])).

thf('517',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('518',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('519',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['516','517','518'])).

thf('520',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('521',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['519','520'])).

thf('522',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('523',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('524',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['521','522','523'])).

thf('525',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['513','524'])).

thf('526',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['513','524'])).

thf('527',plain,(
    ~ ( r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['479','525','526'])).

thf('528',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','269','270','271','272'])).

thf('529',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('530',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['528','529'])).

thf('531',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('532',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('533',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('534',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_funct_1 @ k1_xboole_0 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['530','531','532','533'])).

thf('535',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('536',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('537',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['535','536'])).

thf('538',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('539',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('540',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['537','538','539'])).

thf('541',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('542',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('543',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['541','542'])).

thf('544',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('545',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('546',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['543','544','545'])).

thf('547',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_funct_2 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('548',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['546','547'])).

thf('549',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('550',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('551',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('552',plain,
    ( ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['550','551'])).

thf('553',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('554',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('555',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['552','553','554'])).

thf('556',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['548','549','555'])).

thf('557',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('558',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('559',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('560',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('561',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('562',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('563',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('564',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('565',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['556','557','558','559','560','561','562','563','564'])).

thf('566',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['540','565'])).

thf('567',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('568',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['262'])).

thf('569',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('570',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('571',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('572',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['570','571'])).

thf('573',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['572'])).

thf('574',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('575',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['573','574'])).

thf('576',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('577',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('578',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('579',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('580',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('581',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['579','580'])).

thf('582',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['578','581'])).

thf('583',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['582'])).

thf('584',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['577','583'])).

thf('585',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['584'])).

thf('586',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['576','585'])).

thf('587',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['586'])).

thf('588',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['572'])).

thf('589',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('590',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['588','589'])).

thf('591',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['587','590'])).

thf('592',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['591'])).

thf('593',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['575','592'])).

thf('594',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['593'])).

thf('595',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['569','594'])).

thf('596',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['595'])).

thf('597',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['568','596'])).

thf('598',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('599',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('600',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('601',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['597','598','599','600'])).

thf('602',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['567','601'])).

thf('603',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('604',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('605',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('606',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['602','603','604','605'])).

thf('607',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['606'])).

thf('608',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('609',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['607','608'])).

thf('610',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('611',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('612',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('613',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['611','612'])).

thf('614',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('615',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('616',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('617',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['613','614','615','616'])).

thf('618',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('619',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['617','618'])).

thf('620',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('621',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('622',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['620','621'])).

thf('623',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('624',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('625',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('626',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['622','623','624','625'])).

thf('627',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['619','626'])).

thf('628',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['610','627'])).

thf('629',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('630',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('631',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('632',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['628','629','630','631'])).

thf('633',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('634',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('635',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('636',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('637',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['584'])).

thf('638',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['636','637'])).

thf('639',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['635','638'])).

thf('640',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['639'])).

thf('641',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['634','640'])).

thf('642',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['641'])).

thf('643',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['633','642'])).

thf('644',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['643'])).

thf('645',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['632','644'])).

thf('646',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('647',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('648',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('649',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['645','646','647','648'])).

thf('650',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('651',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['649','650'])).

thf('652',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('653',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('654',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['651','652','653'])).

thf('655',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['265','266','267','268'])).

thf('656',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('657',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('658',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('659',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('660',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('661',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['586'])).

thf('662',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['572'])).

thf('663',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['277'])).

thf('664',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_funct_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['662','663'])).

thf('665',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['661','664'])).

thf('666',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_funct_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['665'])).

thf('667',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['660','666'])).

thf('668',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['667'])).

thf('669',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['659','668'])).

thf('670',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['658','669'])).

thf('671',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['670'])).

thf('672',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['657','671'])).

thf('673',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['672'])).

thf('674',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['656','673'])).

thf('675',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X0 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['674'])).

thf('676',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['655','675'])).

thf('677',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['628','629','630','631'])).

thf('678',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['275','282','283','284','285'])).

thf('679',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['677','678'])).

thf('680',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('681',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('682',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('683',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['676','679','680','681','682'])).

thf('684',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('685',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('686',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('687',plain,(
    r2_funct_2 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['683','684','685','686'])).

thf('688',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['566','609','654','687'])).

thf('689',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_funct_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['534','688'])).

thf('690',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['442','443'])).

thf('691',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('692',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['690','691'])).

thf('693',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['513','524'])).

thf('694',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['692','693'])).

thf('695',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ k1_xboole_0 @ X27 )
      | ( v1_partfun1 @ X28 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(simplify,[status(thm)],['339'])).

thf('696',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['694','695'])).

thf('697',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('698',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('699',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['697','698'])).

thf('700',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['447','448'])).

thf('701',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('702',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['700','701'])).

thf('703',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['513','524'])).

thf('704',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['702','703'])).

thf('705',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['696','699','704'])).

thf('706',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('707',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['705','706'])).

thf('708',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('709',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('710',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['708','709'])).

thf('711',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('712',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('713',plain,(
    v4_relat_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['711','712'])).

thf('714',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['513','524'])).

thf('715',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['713','714'])).

thf('716',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['707','710','715'])).

thf('717',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['689','716'])).

thf('718',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['521','522','523'])).

thf('719',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['513','524'])).

thf('720',plain,(
    r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['718','719'])).

thf('721',plain,(
    $false ),
    inference(demod,[status(thm)],['527','717','720'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4BSkZAXumu
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 46.64/46.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 46.64/46.88  % Solved by: fo/fo7.sh
% 46.64/46.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 46.64/46.88  % done 13607 iterations in 46.408s
% 46.64/46.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 46.64/46.88  % SZS output start Refutation
% 46.64/46.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 46.64/46.88  thf(sk_B_type, type, sk_B: $i).
% 46.64/46.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 46.64/46.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 46.64/46.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 46.64/46.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 46.64/46.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 46.64/46.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 46.64/46.88  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 46.64/46.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 46.64/46.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 46.64/46.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 46.64/46.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 46.64/46.88  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 46.64/46.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 46.64/46.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 46.64/46.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 46.64/46.88  thf(sk_C_type, type, sk_C: $i).
% 46.64/46.88  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 46.64/46.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 46.64/46.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 46.64/46.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 46.64/46.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 46.64/46.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 46.64/46.88  thf(sk_A_type, type, sk_A: $i).
% 46.64/46.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 46.64/46.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 46.64/46.88  thf(d3_struct_0, axiom,
% 46.64/46.88    (![A:$i]:
% 46.64/46.88     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 46.64/46.88  thf('0', plain,
% 46.64/46.88      (![X34 : $i]:
% 46.64/46.88         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.88  thf('1', plain,
% 46.64/46.88      (![X34 : $i]:
% 46.64/46.88         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.88  thf('2', plain,
% 46.64/46.88      (![X34 : $i]:
% 46.64/46.88         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.88  thf(t64_tops_2, conjecture,
% 46.64/46.88    (![A:$i]:
% 46.64/46.88     ( ( l1_struct_0 @ A ) =>
% 46.64/46.88       ( ![B:$i]:
% 46.64/46.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 46.64/46.88           ( ![C:$i]:
% 46.64/46.88             ( ( ( v1_funct_1 @ C ) & 
% 46.64/46.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 46.64/46.88                 ( m1_subset_1 @
% 46.64/46.88                   C @ 
% 46.64/46.88                   ( k1_zfmisc_1 @
% 46.64/46.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 46.64/46.88               ( ( ( ( k2_relset_1 @
% 46.64/46.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 46.64/46.88                     ( k2_struct_0 @ B ) ) & 
% 46.64/46.88                   ( v2_funct_1 @ C ) ) =>
% 46.64/46.88                 ( r2_funct_2 @
% 46.64/46.88                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 46.64/46.88                   ( k2_tops_2 @
% 46.64/46.89                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 46.64/46.89                     ( k2_tops_2 @
% 46.64/46.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 46.64/46.89                   C ) ) ) ) ) ) ))).
% 46.64/46.89  thf(zf_stmt_0, negated_conjecture,
% 46.64/46.89    (~( ![A:$i]:
% 46.64/46.89        ( ( l1_struct_0 @ A ) =>
% 46.64/46.89          ( ![B:$i]:
% 46.64/46.89            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 46.64/46.89              ( ![C:$i]:
% 46.64/46.89                ( ( ( v1_funct_1 @ C ) & 
% 46.64/46.89                    ( v1_funct_2 @
% 46.64/46.89                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 46.64/46.89                    ( m1_subset_1 @
% 46.64/46.89                      C @ 
% 46.64/46.89                      ( k1_zfmisc_1 @
% 46.64/46.89                        ( k2_zfmisc_1 @
% 46.64/46.89                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 46.64/46.89                  ( ( ( ( k2_relset_1 @
% 46.64/46.89                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 46.64/46.89                        ( k2_struct_0 @ B ) ) & 
% 46.64/46.89                      ( v2_funct_1 @ C ) ) =>
% 46.64/46.89                    ( r2_funct_2 @
% 46.64/46.89                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 46.64/46.89                      ( k2_tops_2 @
% 46.64/46.89                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 46.64/46.89                        ( k2_tops_2 @
% 46.64/46.89                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 46.64/46.89                      C ) ) ) ) ) ) ) )),
% 46.64/46.89    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 46.64/46.89  thf('3', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('4', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup-', [status(thm)], ['2', '3'])).
% 46.64/46.89  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('6', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['4', '5'])).
% 46.64/46.89  thf('7', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('8', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('9', plain,
% 46.64/46.89      (((m1_subset_1 @ sk_C @ 
% 46.64/46.89         (k1_zfmisc_1 @ 
% 46.64/46.89          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['7', '8'])).
% 46.64/46.89  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('11', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['9', '10'])).
% 46.64/46.89  thf(d4_tops_2, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 46.64/46.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.64/46.89       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 46.64/46.89         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 46.64/46.89  thf('12', plain,
% 46.64/46.89      (![X35 : $i, X36 : $i, X37 : $i]:
% 46.64/46.89         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 46.64/46.89          | ~ (v2_funct_1 @ X37)
% 46.64/46.89          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 46.64/46.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 46.64/46.89          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 46.64/46.89          | ~ (v1_funct_1 @ X37))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_tops_2])).
% 46.64/46.89  thf('13', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89            = (k2_funct_1 @ sk_C))
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89            != (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['11', '12'])).
% 46.64/46.89  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('15', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('16', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('17', plain,
% 46.64/46.89      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['15', '16'])).
% 46.64/46.89  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('19', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('20', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('21', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('22', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('23', plain,
% 46.64/46.89      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89          = (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['21', '22'])).
% 46.64/46.89  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('25', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['23', '24'])).
% 46.64/46.89  thf('26', plain,
% 46.64/46.89      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89          = (k2_funct_1 @ sk_C))
% 46.64/46.89        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('demod', [status(thm)], ['13', '14', '19', '20', '25'])).
% 46.64/46.89  thf('27', plain,
% 46.64/46.89      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_funct_1 @ sk_C))),
% 46.64/46.89      inference('simplify', [status(thm)], ['26'])).
% 46.64/46.89  thf('28', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['6', '27'])).
% 46.64/46.89  thf('29', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup-', [status(thm)], ['1', '28'])).
% 46.64/46.89  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('31', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['29', '30'])).
% 46.64/46.89  thf('32', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup-', [status(thm)], ['0', '31'])).
% 46.64/46.89  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('34', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['32', '33'])).
% 46.64/46.89  thf(t65_funct_1, axiom,
% 46.64/46.89    (![A:$i]:
% 46.64/46.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 46.64/46.89       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 46.64/46.89  thf('35', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('36', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('37', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf(t132_funct_2, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( ( v1_funct_1 @ C ) & 
% 46.64/46.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.64/46.89       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 46.64/46.89           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.64/46.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 46.64/46.89           ( v1_partfun1 @ C @ A ) ) ) ))).
% 46.64/46.89  thf('38', plain,
% 46.64/46.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 46.64/46.89         (((X27) = (k1_xboole_0))
% 46.64/46.89          | ~ (v1_funct_1 @ X28)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 46.64/46.89          | (v1_partfun1 @ X28 @ X29)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 46.64/46.89          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 46.64/46.89          | ~ (v1_funct_1 @ X28))),
% 46.64/46.89      inference('cnf', [status(esa)], [t132_funct_2])).
% 46.64/46.89  thf('39', plain,
% 46.64/46.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 46.64/46.89         (~ (v1_funct_2 @ X28 @ X29 @ X27)
% 46.64/46.89          | (v1_partfun1 @ X28 @ X29)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 46.64/46.89          | ~ (v1_funct_1 @ X28)
% 46.64/46.89          | ((X27) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['38'])).
% 46.64/46.89  thf('40', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['37', '39'])).
% 46.64/46.89  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('42', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('43', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['40', '41', '42'])).
% 46.64/46.89  thf(d4_partfun1, axiom,
% 46.64/46.89    (![A:$i,B:$i]:
% 46.64/46.89     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 46.64/46.89       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 46.64/46.89  thf('44', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('45', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['43', '44'])).
% 46.64/46.89  thf('46', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf(cc2_relat_1, axiom,
% 46.64/46.89    (![A:$i]:
% 46.64/46.89     ( ( v1_relat_1 @ A ) =>
% 46.64/46.89       ( ![B:$i]:
% 46.64/46.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 46.64/46.89  thf('47', plain,
% 46.64/46.89      (![X0 : $i, X1 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 46.64/46.89          | (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X1))),
% 46.64/46.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 46.64/46.89  thf('48', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ 
% 46.64/46.89           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 46.64/46.89        | (v1_relat_1 @ sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['46', '47'])).
% 46.64/46.89  thf(fc6_relat_1, axiom,
% 46.64/46.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 46.64/46.89  thf('49', plain,
% 46.64/46.89      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 46.64/46.89  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('51', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf(cc2_relset_1, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.64/46.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 46.64/46.89  thf('52', plain,
% 46.64/46.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 46.64/46.89         ((v4_relat_1 @ X7 @ X8)
% 46.64/46.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 46.64/46.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.64/46.89  thf('53', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 46.64/46.89      inference('sup-', [status(thm)], ['51', '52'])).
% 46.64/46.89  thf('54', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['45', '50', '53'])).
% 46.64/46.89  thf('55', plain,
% 46.64/46.89      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['36', '54'])).
% 46.64/46.89  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('57', plain,
% 46.64/46.89      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['55', '56'])).
% 46.64/46.89  thf('58', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('59', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['6', '27'])).
% 46.64/46.89  thf('60', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ~ (l1_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup-', [status(thm)], ['58', '59'])).
% 46.64/46.89  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('62', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['60', '61'])).
% 46.64/46.89  thf('63', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 46.64/46.89            (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['57', '62'])).
% 46.64/46.89  thf('64', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf(redefinition_k2_relset_1, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.64/46.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 46.64/46.89  thf('65', plain,
% 46.64/46.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 46.64/46.89         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 46.64/46.89          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 46.64/46.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 46.64/46.89  thf('66', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_relat_1 @ sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['64', '65'])).
% 46.64/46.89  thf('67', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf(fc6_funct_1, axiom,
% 46.64/46.89    (![A:$i]:
% 46.64/46.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 46.64/46.89       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 46.64/46.89         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 46.64/46.89         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 46.64/46.89  thf('69', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('70', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('71', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf(t55_funct_1, axiom,
% 46.64/46.89    (![A:$i]:
% 46.64/46.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 46.64/46.89       ( ( v2_funct_1 @ A ) =>
% 46.64/46.89         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 46.64/46.89           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 46.64/46.89  thf('72', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf(t3_funct_2, axiom,
% 46.64/46.89    (![A:$i]:
% 46.64/46.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 46.64/46.89       ( ( v1_funct_1 @ A ) & 
% 46.64/46.89         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 46.64/46.89         ( m1_subset_1 @
% 46.64/46.89           A @ 
% 46.64/46.89           ( k1_zfmisc_1 @
% 46.64/46.89             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 46.64/46.89  thf('73', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X33 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('74', plain,
% 46.64/46.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 46.64/46.89         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 46.64/46.89          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 46.64/46.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 46.64/46.89  thf('75', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['73', '74'])).
% 46.64/46.89  thf('76', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('77', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X33 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('78', plain,
% 46.64/46.89      (![X35 : $i, X36 : $i, X37 : $i]:
% 46.64/46.89         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 46.64/46.89          | ~ (v2_funct_1 @ X37)
% 46.64/46.89          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 46.64/46.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 46.64/46.89          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 46.64/46.89          | ~ (v1_funct_1 @ X37))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_tops_2])).
% 46.64/46.89  thf('79', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              != (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['77', '78'])).
% 46.64/46.89  thf('80', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89            != (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['79'])).
% 46.64/46.89  thf('81', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              != (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['76', '80'])).
% 46.64/46.89  thf('82', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89            != (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['81'])).
% 46.64/46.89  thf('83', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['75', '82'])).
% 46.64/46.89  thf('84', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 46.64/46.89              = (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['83'])).
% 46.64/46.89  thf('85', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['72', '84'])).
% 46.64/46.89  thf('86', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ 
% 46.64/46.89              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 46.64/46.89              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['71', '85'])).
% 46.64/46.89  thf('87', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['86'])).
% 46.64/46.89  thf('88', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ 
% 46.64/46.89              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 46.64/46.89              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['70', '87'])).
% 46.64/46.89  thf('89', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['88'])).
% 46.64/46.89  thf('90', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ 
% 46.64/46.89              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 46.64/46.89              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['69', '89'])).
% 46.64/46.89  thf('91', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['90'])).
% 46.64/46.89  thf('92', plain,
% 46.64/46.89      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 46.64/46.89          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['68', '91'])).
% 46.64/46.89  thf('93', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('94', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('95', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('96', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('97', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('98', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('99', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('100', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('101', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('102', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('103', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('104', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('105', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('106', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('107', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X33 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('108', plain,
% 46.64/46.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 46.64/46.89         ((v4_relat_1 @ X7 @ X8)
% 46.64/46.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 46.64/46.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.64/46.89  thf('109', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['107', '108'])).
% 46.64/46.89  thf('110', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['106', '109'])).
% 46.64/46.89  thf('111', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['105', '110'])).
% 46.64/46.89  thf('112', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['111'])).
% 46.64/46.89  thf('113', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['104', '112'])).
% 46.64/46.89  thf('114', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['113'])).
% 46.64/46.89  thf('115', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['103', '114'])).
% 46.64/46.89  thf('116', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['102', '115'])).
% 46.64/46.89  thf('117', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['116'])).
% 46.64/46.89  thf('118', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['101', '117'])).
% 46.64/46.89  thf('119', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['118'])).
% 46.64/46.89  thf('120', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['100', '119'])).
% 46.64/46.89  thf('121', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['120'])).
% 46.64/46.89  thf('122', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['99', '121'])).
% 46.64/46.89  thf('123', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['98', '122'])).
% 46.64/46.89  thf('124', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['123'])).
% 46.64/46.89  thf('125', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['97', '124'])).
% 46.64/46.89  thf('126', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['125'])).
% 46.64/46.89  thf('127', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['96', '126'])).
% 46.64/46.89  thf('128', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['127'])).
% 46.64/46.89  thf('129', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('130', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('131', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('132', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('133', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('134', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('135', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('136', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('137', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('138', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('139', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('140', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['107', '108'])).
% 46.64/46.89  thf('141', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (((k1_relat_1 @ X22) != (X21))
% 46.64/46.89          | (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('142', plain,
% 46.64/46.89      (![X22 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X22)
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ (k1_relat_1 @ X22))
% 46.64/46.89          | (v1_partfun1 @ X22 @ (k1_relat_1 @ X22)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['141'])).
% 46.64/46.89  thf('143', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['140', '142'])).
% 46.64/46.89  thf('144', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['143'])).
% 46.64/46.89  thf('145', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['139', '144'])).
% 46.64/46.89  thf('146', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['138', '145'])).
% 46.64/46.89  thf('147', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['146'])).
% 46.64/46.89  thf('148', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['137', '147'])).
% 46.64/46.89  thf('149', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['148'])).
% 46.64/46.89  thf('150', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['136', '149'])).
% 46.64/46.89  thf('151', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['135', '150'])).
% 46.64/46.89  thf('152', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['151'])).
% 46.64/46.89  thf('153', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['134', '152'])).
% 46.64/46.89  thf('154', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['153'])).
% 46.64/46.89  thf('155', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['133', '154'])).
% 46.64/46.89  thf('156', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['155'])).
% 46.64/46.89  thf('157', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['132', '156'])).
% 46.64/46.89  thf('158', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['131', '157'])).
% 46.64/46.89  thf('159', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['158'])).
% 46.64/46.89  thf('160', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['130', '159'])).
% 46.64/46.89  thf('161', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['160'])).
% 46.64/46.89  thf('162', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['129', '161'])).
% 46.64/46.89  thf('163', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['162'])).
% 46.64/46.89  thf('164', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('165', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89               (k2_relat_1 @ X0))
% 46.64/46.89          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89              = (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['163', '164'])).
% 46.64/46.89  thf('166', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89              = (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['128', '165'])).
% 46.64/46.89  thf('167', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89              = (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['166'])).
% 46.64/46.89  thf('168', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89              = (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['95', '167'])).
% 46.64/46.89  thf('169', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89            = (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['168'])).
% 46.64/46.89  thf('170', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89              = (k2_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['94', '169'])).
% 46.64/46.89  thf('171', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89            = (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['170'])).
% 46.64/46.89  thf('172', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('173', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('174', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('175', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('176', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('177', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('178', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('179', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('180', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('181', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X33 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('182', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['180', '181'])).
% 46.64/46.89  thf('183', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['179', '182'])).
% 46.64/46.89  thf('184', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['183'])).
% 46.64/46.89  thf('185', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['178', '184'])).
% 46.64/46.89  thf('186', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['185'])).
% 46.64/46.89  thf('187', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['177', '186'])).
% 46.64/46.89  thf('188', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89               (k2_relat_1 @ X0)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['176', '187'])).
% 46.64/46.89  thf('189', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['188'])).
% 46.64/46.89  thf('190', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89               (k2_relat_1 @ X0)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['175', '189'])).
% 46.64/46.89  thf('191', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['190'])).
% 46.64/46.89  thf('192', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89               (k2_relat_1 @ X0)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['174', '191'])).
% 46.64/46.89  thf('193', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['192'])).
% 46.64/46.89  thf('194', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['173', '193'])).
% 46.64/46.89  thf('195', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['194'])).
% 46.64/46.89  thf('196', plain,
% 46.64/46.89      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89         (k1_zfmisc_1 @ 
% 46.64/46.89          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['172', '195'])).
% 46.64/46.89  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('200', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 46.64/46.89  thf('201', plain,
% 46.64/46.89      (![X0 : $i, X1 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 46.64/46.89          | (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X1))),
% 46.64/46.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 46.64/46.89  thf('202', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ 
% 46.64/46.89           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))
% 46.64/46.89        | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['200', '201'])).
% 46.64/46.89  thf('203', plain,
% 46.64/46.89      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 46.64/46.89  thf('204', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['202', '203'])).
% 46.64/46.89  thf('205', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('206', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('207', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('208', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('209', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('210', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['127'])).
% 46.64/46.89  thf('211', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['209', '210'])).
% 46.64/46.89  thf('212', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['208', '211'])).
% 46.64/46.89  thf('213', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['212'])).
% 46.64/46.89  thf('214', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v4_relat_1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['207', '213'])).
% 46.64/46.89  thf('215', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['214'])).
% 46.64/46.89  thf('216', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v4_relat_1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['206', '215'])).
% 46.64/46.89  thf('217', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['216'])).
% 46.64/46.89  thf('218', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('219', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('220', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('221', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('222', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89           (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['162'])).
% 46.64/46.89  thf('223', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['221', '222'])).
% 46.64/46.89  thf('224', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['220', '223'])).
% 46.64/46.89  thf('225', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['224'])).
% 46.64/46.89  thf('226', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_partfun1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['219', '225'])).
% 46.64/46.89  thf('227', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['226'])).
% 46.64/46.89  thf('228', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_partfun1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['218', '227'])).
% 46.64/46.89  thf('229', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['228'])).
% 46.64/46.89  thf('230', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('231', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ 
% 46.64/46.89               (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v4_relat_1 @ 
% 46.64/46.89               (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 46.64/46.89               (k1_relat_1 @ X0))
% 46.64/46.89          | ((k1_relat_1 @ 
% 46.64/46.89              (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89              = (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['229', '230'])).
% 46.64/46.89  thf('232', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k1_relat_1 @ 
% 46.64/46.89              (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89              = (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ 
% 46.64/46.89               (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['217', '231'])).
% 46.64/46.89  thf('233', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ((k1_relat_1 @ 
% 46.64/46.89              (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89              = (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['232'])).
% 46.64/46.89  thf('234', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k1_relat_1 @ 
% 46.64/46.89              (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89              = (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['205', '233'])).
% 46.64/46.89  thf('235', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k1_relat_1 @ 
% 46.64/46.89            (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89            = (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['234'])).
% 46.64/46.89  thf('236', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((k1_relat_1 @ 
% 46.64/46.89            (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 46.64/46.89            = (k1_relat_1 @ sk_C)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['204', '235'])).
% 46.64/46.89  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('240', plain,
% 46.64/46.89      (((k1_relat_1 @ 
% 46.64/46.89         (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 46.64/46.89         = (k1_relat_1 @ sk_C))),
% 46.64/46.89      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 46.64/46.89  thf('241', plain,
% 46.64/46.89      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 46.64/46.89        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['171', '240'])).
% 46.64/46.89  thf('242', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['9', '10'])).
% 46.64/46.89  thf(t31_funct_2, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 46.64/46.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.64/46.89       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 46.64/46.89         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 46.64/46.89           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 46.64/46.89           ( m1_subset_1 @
% 46.64/46.89             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 46.64/46.89  thf('243', plain,
% 46.64/46.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X30)
% 46.64/46.89          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ X30) @ 
% 46.64/46.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 46.64/46.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 46.64/46.89          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 46.64/46.89          | ~ (v1_funct_1 @ X30))),
% 46.64/46.89      inference('cnf', [status(esa)], [t31_funct_2])).
% 46.64/46.89  thf('244', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 46.64/46.89        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89            != (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['242', '243'])).
% 46.64/46.89  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('246', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('247', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['23', '24'])).
% 46.64/46.89  thf('248', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('249', plain,
% 46.64/46.89      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 46.64/46.89         (k1_zfmisc_1 @ 
% 46.64/46.89          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 46.64/46.89        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('demod', [status(thm)], ['244', '245', '246', '247', '248'])).
% 46.64/46.89  thf('250', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['249'])).
% 46.64/46.89  thf('251', plain,
% 46.64/46.89      (![X0 : $i, X1 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 46.64/46.89          | (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X1))),
% 46.64/46.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 46.64/46.89  thf('252', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ 
% 46.64/46.89           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 46.64/46.89        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['250', '251'])).
% 46.64/46.89  thf('253', plain,
% 46.64/46.89      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 46.64/46.89  thf('254', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 46.64/46.89      inference('demod', [status(thm)], ['252', '253'])).
% 46.64/46.89  thf('255', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['9', '10'])).
% 46.64/46.89  thf('256', plain,
% 46.64/46.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X30)
% 46.64/46.89          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ X30))
% 46.64/46.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 46.64/46.89          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 46.64/46.89          | ~ (v1_funct_1 @ X30))),
% 46.64/46.89      inference('cnf', [status(esa)], [t31_funct_2])).
% 46.64/46.89  thf('257', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89            != (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['255', '256'])).
% 46.64/46.89  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('259', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('260', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['23', '24'])).
% 46.64/46.89  thf('261', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('262', plain,
% 46.64/46.89      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('demod', [status(thm)], ['257', '258', '259', '260', '261'])).
% 46.64/46.89  thf('263', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 46.64/46.89      inference('simplify', [status(thm)], ['262'])).
% 46.64/46.89  thf('264', plain,
% 46.64/46.89      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 46.64/46.89        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['241', '254', '263'])).
% 46.64/46.89  thf('265', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['93', '264'])).
% 46.64/46.89  thf('266', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('267', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('268', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('269', plain,
% 46.64/46.89      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 46.64/46.89      inference('demod', [status(thm)], ['265', '266', '267', '268'])).
% 46.64/46.89  thf('270', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('271', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('272', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('273', plain,
% 46.64/46.89      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 46.64/46.89         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['92', '269', '270', '271', '272'])).
% 46.64/46.89  thf('274', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 46.64/46.89        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['63', '273'])).
% 46.64/46.89  thf('275', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['35', '274'])).
% 46.64/46.89  thf('276', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf(redefinition_r2_funct_2, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i,D:$i]:
% 46.64/46.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 46.64/46.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 46.64/46.89         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 46.64/46.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.64/46.89       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 46.64/46.89  thf('277', plain,
% 46.64/46.89      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 46.64/46.89          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 46.64/46.89          | ~ (v1_funct_1 @ X23)
% 46.64/46.89          | ~ (v1_funct_1 @ X26)
% 46.64/46.89          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 46.64/46.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 46.64/46.89          | (r2_funct_2 @ X24 @ X25 @ X23 @ X26)
% 46.64/46.89          | ((X23) != (X26)))),
% 46.64/46.89      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 46.64/46.89  thf('278', plain,
% 46.64/46.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 46.64/46.89         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 46.64/46.89          | ~ (v1_funct_1 @ X26)
% 46.64/46.89          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 46.64/46.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['277'])).
% 46.64/46.89  thf('279', plain,
% 46.64/46.89      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 46.64/46.89           sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['276', '278'])).
% 46.64/46.89  thf('280', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('282', plain,
% 46.64/46.89      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['279', '280', '281'])).
% 46.64/46.89  thf('283', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('284', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('285', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('286', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('287', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('288', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ 
% 46.64/46.89          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['34', '286', '287'])).
% 46.64/46.89  thf('289', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('290', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('291', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['45', '50', '53'])).
% 46.64/46.89  thf('292', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('293', plain,
% 46.64/46.89      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['291', '292'])).
% 46.64/46.89  thf('294', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['45', '50', '53'])).
% 46.64/46.89  thf('295', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('296', plain,
% 46.64/46.89      (((m1_subset_1 @ sk_C @ 
% 46.64/46.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['294', '295'])).
% 46.64/46.89  thf(d1_funct_2, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.64/46.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 46.64/46.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 46.64/46.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 46.64/46.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 46.64/46.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 46.64/46.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 46.64/46.89  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 46.64/46.89  thf(zf_stmt_2, axiom,
% 46.64/46.89    (![C:$i,B:$i,A:$i]:
% 46.64/46.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 46.64/46.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 46.64/46.89  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 46.64/46.89  thf(zf_stmt_4, axiom,
% 46.64/46.89    (![B:$i,A:$i]:
% 46.64/46.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 46.64/46.89       ( zip_tseitin_0 @ B @ A ) ))).
% 46.64/46.89  thf(zf_stmt_5, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 46.64/46.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 46.64/46.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 46.64/46.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 46.64/46.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 46.64/46.89  thf('297', plain,
% 46.64/46.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 46.64/46.89         (((X18) != (k1_xboole_0))
% 46.64/46.89          | ((X19) = (k1_xboole_0))
% 46.64/46.89          | ((X20) = (k1_xboole_0))
% 46.64/46.89          | ~ (v1_funct_2 @ X20 @ X19 @ X18)
% 46.64/46.89          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 46.64/46.89  thf('298', plain,
% 46.64/46.89      (![X19 : $i, X20 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X20 @ 
% 46.64/46.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ k1_xboole_0)))
% 46.64/46.89          | ~ (v1_funct_2 @ X20 @ X19 @ k1_xboole_0)
% 46.64/46.89          | ((X20) = (k1_xboole_0))
% 46.64/46.89          | ((X19) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['297'])).
% 46.64/46.89  thf('299', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['296', '298'])).
% 46.64/46.89  thf('300', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['293', '299'])).
% 46.64/46.89  thf('301', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['300'])).
% 46.64/46.89  thf('302', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_A)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['290', '301'])).
% 46.64/46.89  thf('303', plain, ((l1_struct_0 @ sk_A)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('304', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['302', '303'])).
% 46.64/46.89  thf('305', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 46.64/46.89      inference('sup-', [status(thm)], ['51', '52'])).
% 46.64/46.89  thf('306', plain,
% 46.64/46.89      (((v4_relat_1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['304', '305'])).
% 46.64/46.89  thf('307', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['302', '303'])).
% 46.64/46.89  thf('308', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('309', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('310', plain,
% 46.64/46.89      (((m1_subset_1 @ sk_C @ 
% 46.64/46.89         (k1_zfmisc_1 @ 
% 46.64/46.89          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_A))),
% 46.64/46.89      inference('sup+', [status(thm)], ['308', '309'])).
% 46.64/46.89  thf('311', plain, ((l1_struct_0 @ sk_A)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('312', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['310', '311'])).
% 46.64/46.89  thf('313', plain,
% 46.64/46.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 46.64/46.89         (~ (v1_funct_2 @ X28 @ X29 @ X27)
% 46.64/46.89          | (v1_partfun1 @ X28 @ X29)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 46.64/46.89          | ~ (v1_funct_1 @ X28)
% 46.64/46.89          | ((X27) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['38'])).
% 46.64/46.89  thf('314', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['312', '313'])).
% 46.64/46.89  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('316', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('317', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('318', plain,
% 46.64/46.89      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_A))),
% 46.64/46.89      inference('sup+', [status(thm)], ['316', '317'])).
% 46.64/46.89  thf('319', plain, ((l1_struct_0 @ sk_A)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('320', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['318', '319'])).
% 46.64/46.89  thf('321', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['314', '315', '320'])).
% 46.64/46.89  thf('322', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('323', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['321', '322'])).
% 46.64/46.89  thf('324', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('325', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['310', '311'])).
% 46.64/46.89  thf('326', plain,
% 46.64/46.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 46.64/46.89         ((v4_relat_1 @ X7 @ X8)
% 46.64/46.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 46.64/46.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 46.64/46.89  thf('327', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 46.64/46.89      inference('sup-', [status(thm)], ['325', '326'])).
% 46.64/46.89  thf('328', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['323', '324', '327'])).
% 46.64/46.89  thf('329', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('330', plain,
% 46.64/46.89      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['328', '329'])).
% 46.64/46.89  thf('331', plain,
% 46.64/46.89      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['307', '330'])).
% 46.64/46.89  thf('332', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['331'])).
% 46.64/46.89  thf('333', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['302', '303'])).
% 46.64/46.89  thf('334', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('demod', [status(thm)], ['323', '324', '327'])).
% 46.64/46.89  thf('335', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('336', plain,
% 46.64/46.89      (((m1_subset_1 @ sk_C @ 
% 46.64/46.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['334', '335'])).
% 46.64/46.89  thf('337', plain,
% 46.64/46.89      (((m1_subset_1 @ sk_C @ 
% 46.64/46.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['333', '336'])).
% 46.64/46.89  thf('338', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | (m1_subset_1 @ sk_C @ 
% 46.64/46.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['337'])).
% 46.64/46.89  thf('339', plain,
% 46.64/46.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 46.64/46.89         (((X29) != (k1_xboole_0))
% 46.64/46.89          | ~ (v1_funct_1 @ X28)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 46.64/46.89          | (v1_partfun1 @ X28 @ X29)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 46.64/46.89          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 46.64/46.89          | ~ (v1_funct_1 @ X28))),
% 46.64/46.89      inference('cnf', [status(esa)], [t132_funct_2])).
% 46.64/46.89  thf('340', plain,
% 46.64/46.89      (![X27 : $i, X28 : $i]:
% 46.64/46.89         (~ (v1_funct_2 @ X28 @ k1_xboole_0 @ X27)
% 46.64/46.89          | (v1_partfun1 @ X28 @ k1_xboole_0)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ 
% 46.64/46.89               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X27)))
% 46.64/46.89          | ~ (v1_funct_1 @ X28))),
% 46.64/46.89      inference('simplify', [status(thm)], ['339'])).
% 46.64/46.89  thf('341', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['338', '340'])).
% 46.64/46.89  thf('342', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('343', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['341', '342'])).
% 46.64/46.89  thf('344', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['332', '343'])).
% 46.64/46.89  thf('345', plain,
% 46.64/46.89      (((v1_partfun1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['344'])).
% 46.64/46.89  thf('346', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('347', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['345', '346'])).
% 46.64/46.89  thf('348', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('349', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['347', '348'])).
% 46.64/46.89  thf('350', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['306', '349'])).
% 46.64/46.89  thf('351', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['350'])).
% 46.64/46.89  thf('352', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('353', plain,
% 46.64/46.89      (![X13 : $i, X14 : $i]:
% 46.64/46.89         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 46.64/46.89  thf('354', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('355', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('356', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('357', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('358', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('359', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['185'])).
% 46.64/46.89  thf('360', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X0 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['358', '359'])).
% 46.64/46.89  thf('361', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ X0 @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['357', '360'])).
% 46.64/46.89  thf('362', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X0 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['361'])).
% 46.64/46.89  thf('363', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (m1_subset_1 @ X0 @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['356', '362'])).
% 46.64/46.89  thf('364', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X0 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['363'])).
% 46.64/46.89  thf('365', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ X0 @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['355', '364'])).
% 46.64/46.89  thf('366', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X0 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['365'])).
% 46.64/46.89  thf('367', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X0 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['354', '366'])).
% 46.64/46.89  thf('368', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ X0 @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['367'])).
% 46.64/46.89  thf('369', plain,
% 46.64/46.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 46.64/46.89         (~ (zip_tseitin_0 @ X18 @ X19)
% 46.64/46.89          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 46.64/46.89          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 46.64/46.89  thf('370', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (zip_tseitin_0 @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89               (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['368', '369'])).
% 46.64/46.89  thf('371', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) = (k1_xboole_0))
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 46.64/46.89             (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['353', '370'])).
% 46.64/46.89  thf('372', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['352', '371'])).
% 46.64/46.89  thf('373', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) = (k1_xboole_0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['372'])).
% 46.64/46.89  thf('374', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('375', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('376', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('377', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('378', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('379', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('380', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('381', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('382', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('383', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['381', '382'])).
% 46.64/46.89  thf('384', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['380', '383'])).
% 46.64/46.89  thf('385', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['384'])).
% 46.64/46.89  thf('386', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['379', '385'])).
% 46.64/46.89  thf('387', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['386'])).
% 46.64/46.89  thf('388', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['378', '387'])).
% 46.64/46.89  thf('389', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['377', '388'])).
% 46.64/46.89  thf('390', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['389'])).
% 46.64/46.89  thf('391', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['376', '390'])).
% 46.64/46.89  thf('392', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['391'])).
% 46.64/46.89  thf('393', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['375', '392'])).
% 46.64/46.89  thf('394', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['393'])).
% 46.64/46.89  thf('395', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ 
% 46.64/46.89           (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['374', '394'])).
% 46.64/46.89  thf('396', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ 
% 46.64/46.89             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['395'])).
% 46.64/46.89  thf('397', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['373', '396'])).
% 46.64/46.89  thf('398', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ k1_xboole_0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['397'])).
% 46.64/46.89  thf('399', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) = (k1_xboole_0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['372'])).
% 46.64/46.89  thf('400', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ X0 @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ 
% 46.64/46.89               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['367'])).
% 46.64/46.89  thf('401', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X0 @ 
% 46.64/46.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ k1_xboole_0)))
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['399', '400'])).
% 46.64/46.89  thf('402', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | (m1_subset_1 @ X0 @ 
% 46.64/46.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ k1_xboole_0))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['401'])).
% 46.64/46.89  thf('403', plain,
% 46.64/46.89      (![X19 : $i, X20 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X20 @ 
% 46.64/46.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ k1_xboole_0)))
% 46.64/46.89          | ~ (v1_funct_2 @ X20 @ X19 @ k1_xboole_0)
% 46.64/46.89          | ((X20) = (k1_xboole_0))
% 46.64/46.89          | ((X19) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['297'])).
% 46.64/46.89  thf('404', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 46.64/46.89          | ((X0) = (k1_xboole_0))
% 46.64/46.89          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ k1_xboole_0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['402', '403'])).
% 46.64/46.89  thf('405', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((X0) = (k1_xboole_0))
% 46.64/46.89          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['398', '404'])).
% 46.64/46.89  thf('406', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 46.64/46.89          | ((X0) = (k1_xboole_0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['405'])).
% 46.64/46.89  thf('407', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('408', plain,
% 46.64/46.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 46.64/46.89         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 46.64/46.89          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 46.64/46.89          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 46.64/46.89  thf('409', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 46.64/46.89          | ((k1_relat_1 @ X0)
% 46.64/46.89              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['407', '408'])).
% 46.64/46.89  thf('410', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((X0) = (k1_xboole_0))
% 46.64/46.89          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 46.64/46.89          | ((k1_relat_1 @ X0)
% 46.64/46.89              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['406', '409'])).
% 46.64/46.89  thf('411', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k1_relat_1 @ X0)
% 46.64/46.89            = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 46.64/46.89          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 46.64/46.89          | ((X0) = (k1_xboole_0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['410'])).
% 46.64/46.89  thf('412', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C)
% 46.64/46.89          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['351', '411'])).
% 46.64/46.89  thf('413', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('414', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('415', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('416', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('417', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C)
% 46.64/46.89          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['412', '413', '414', '415', '416'])).
% 46.64/46.89  thf('418', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C)
% 46.64/46.89            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['417'])).
% 46.64/46.89  thf('419', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('420', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['350'])).
% 46.64/46.89  thf('421', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 46.64/46.89          | ((X0) = (k1_xboole_0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['405'])).
% 46.64/46.89  thf('422', plain,
% 46.64/46.89      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['420', '421'])).
% 46.64/46.89  thf('423', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('424', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('425', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('426', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('427', plain,
% 46.64/46.89      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['422', '423', '424', '425', '426'])).
% 46.64/46.89  thf('428', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['427'])).
% 46.64/46.89  thf('429', plain,
% 46.64/46.89      (![X34 : $i]:
% 46.64/46.89         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 46.64/46.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 46.64/46.89  thf('430', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('431', plain,
% 46.64/46.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 46.64/46.89         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 46.64/46.89          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 46.64/46.89          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 46.64/46.89  thf('432', plain,
% 46.64/46.89      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 46.64/46.89        | ((u1_struct_0 @ sk_A)
% 46.64/46.89            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['430', '431'])).
% 46.64/46.89  thf('433', plain,
% 46.64/46.89      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_A)
% 46.64/46.89        | ((u1_struct_0 @ sk_A)
% 46.64/46.89            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['429', '432'])).
% 46.64/46.89  thf('434', plain, ((l1_struct_0 @ sk_A)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('435', plain,
% 46.64/46.89      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 46.64/46.89        | ((u1_struct_0 @ sk_A)
% 46.64/46.89            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['433', '434'])).
% 46.64/46.89  thf('436', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A)
% 46.64/46.89            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['428', '435'])).
% 46.64/46.89  thf('437', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A)
% 46.64/46.89          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 46.64/46.89        | ~ (l1_struct_0 @ sk_A)
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['419', '436'])).
% 46.64/46.89  thf('438', plain, ((l1_struct_0 @ sk_A)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('439', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A)
% 46.64/46.89          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['437', '438'])).
% 46.64/46.89  thf('440', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['418', '439'])).
% 46.64/46.89  thf('441', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['440'])).
% 46.64/46.89  thf('442', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['9', '10'])).
% 46.64/46.89  thf('443', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('444', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['442', '443'])).
% 46.64/46.89  thf('445', plain,
% 46.64/46.89      (![X19 : $i, X20 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X20 @ 
% 46.64/46.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ k1_xboole_0)))
% 46.64/46.89          | ~ (v1_funct_2 @ X20 @ X19 @ k1_xboole_0)
% 46.64/46.89          | ((X20) = (k1_xboole_0))
% 46.64/46.89          | ((X19) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['297'])).
% 46.64/46.89  thf('446', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['444', '445'])).
% 46.64/46.89  thf('447', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('448', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('449', plain, ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['447', '448'])).
% 46.64/46.89  thf('450', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['446', '449'])).
% 46.64/46.89  thf('451', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['441', '450'])).
% 46.64/46.89  thf('452', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['451'])).
% 46.64/46.89  thf('453', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('454', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['90'])).
% 46.64/46.89  thf('455', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['453', '454'])).
% 46.64/46.89  thf('456', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89              (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['455'])).
% 46.64/46.89  thf('457', plain,
% 46.64/46.89      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 46.64/46.89          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['452', '456'])).
% 46.64/46.89  thf('458', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('459', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('460', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['458', '459'])).
% 46.64/46.89  thf('461', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('462', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('463', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('464', plain,
% 46.64/46.89      ((((k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 46.64/46.89          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['457', '460', '461', '462', '463'])).
% 46.64/46.89  thf('465', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['446', '449'])).
% 46.64/46.89  thf('466', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['60', '61'])).
% 46.64/46.89  thf('467', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('468', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89          sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['466', '467'])).
% 46.64/46.89  thf('469', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['465', '468'])).
% 46.64/46.89  thf('470', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['464', '469'])).
% 46.64/46.89  thf('471', plain,
% 46.64/46.89      ((((sk_C) = (k1_xboole_0))
% 46.64/46.89        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C))),
% 46.64/46.89      inference('simplify', [status(thm)], ['470'])).
% 46.64/46.89  thf('472', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 46.64/46.89           sk_C)
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((sk_C) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['289', '471'])).
% 46.64/46.89  thf('473', plain,
% 46.64/46.89      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['279', '280', '281'])).
% 46.64/46.89  thf('474', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('475', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('476', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('477', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('478', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('479', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ 
% 46.64/46.89          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89          k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['288', '477', '478'])).
% 46.64/46.89  thf('480', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['249'])).
% 46.64/46.89  thf(dt_k2_tops_2, axiom,
% 46.64/46.89    (![A:$i,B:$i,C:$i]:
% 46.64/46.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 46.64/46.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 46.64/46.89       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 46.64/46.89         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 46.64/46.89         ( m1_subset_1 @
% 46.64/46.89           ( k2_tops_2 @ A @ B @ C ) @ 
% 46.64/46.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 46.64/46.89  thf('481', plain,
% 46.64/46.89      (![X38 : $i, X39 : $i, X40 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_tops_2 @ X38 @ X39 @ X40) @ 
% 46.64/46.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 46.64/46.89          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 46.64/46.89          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 46.64/46.89          | ~ (v1_funct_1 @ X40))),
% 46.64/46.89      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 46.64/46.89  thf('482', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89             (u1_struct_0 @ sk_A))
% 46.64/46.89        | (m1_subset_1 @ 
% 46.64/46.89           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['480', '481'])).
% 46.64/46.89  thf('483', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 46.64/46.89      inference('simplify', [status(thm)], ['262'])).
% 46.64/46.89  thf('484', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['9', '10'])).
% 46.64/46.89  thf('485', plain,
% 46.64/46.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X30)
% 46.64/46.89          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X30) @ X31 @ X32)
% 46.64/46.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 46.64/46.89          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 46.64/46.89          | ~ (v1_funct_1 @ X30))),
% 46.64/46.89      inference('cnf', [status(esa)], [t31_funct_2])).
% 46.64/46.89  thf('486', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89           (u1_struct_0 @ sk_A))
% 46.64/46.89        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89            != (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['484', '485'])).
% 46.64/46.89  thf('487', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('488', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('489', plain,
% 46.64/46.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 46.64/46.89         = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['23', '24'])).
% 46.64/46.89  thf('490', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('491', plain,
% 46.64/46.89      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89         (u1_struct_0 @ sk_A))
% 46.64/46.89        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('demod', [status(thm)], ['486', '487', '488', '489', '490'])).
% 46.64/46.89  thf('492', plain,
% 46.64/46.89      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89        (u1_struct_0 @ sk_A))),
% 46.64/46.89      inference('simplify', [status(thm)], ['491'])).
% 46.64/46.89  thf('493', plain,
% 46.64/46.89      ((m1_subset_1 @ 
% 46.64/46.89        (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89         (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['482', '483', '492'])).
% 46.64/46.89  thf('494', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('495', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('496', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('497', plain,
% 46.64/46.89      ((m1_subset_1 @ 
% 46.64/46.89        (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89         (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['493', '494', '495', '496'])).
% 46.64/46.89  thf('498', plain,
% 46.64/46.89      (![X19 : $i, X20 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X20 @ 
% 46.64/46.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ k1_xboole_0)))
% 46.64/46.89          | ~ (v1_funct_2 @ X20 @ X19 @ k1_xboole_0)
% 46.64/46.89          | ((X20) = (k1_xboole_0))
% 46.64/46.89          | ((X19) = (k1_xboole_0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['297'])).
% 46.64/46.89  thf('499', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 46.64/46.89        | ((k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ k1_xboole_0)) = (k1_xboole_0))
% 46.64/46.89        | ~ (v1_funct_2 @ 
% 46.64/46.89             (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89              (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89             (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['497', '498'])).
% 46.64/46.89  thf('500', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['249'])).
% 46.64/46.89  thf('501', plain,
% 46.64/46.89      (![X38 : $i, X39 : $i, X40 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_tops_2 @ X38 @ X39 @ X40) @ X39 @ X38)
% 46.64/46.89          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 46.64/46.89          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 46.64/46.89          | ~ (v1_funct_1 @ X40))),
% 46.64/46.89      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 46.64/46.89  thf('502', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89             (u1_struct_0 @ sk_A))
% 46.64/46.89        | (v1_funct_2 @ 
% 46.64/46.89           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89           (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['500', '501'])).
% 46.64/46.89  thf('503', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 46.64/46.89      inference('simplify', [status(thm)], ['262'])).
% 46.64/46.89  thf('504', plain,
% 46.64/46.89      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 46.64/46.89        (u1_struct_0 @ sk_A))),
% 46.64/46.89      inference('simplify', [status(thm)], ['491'])).
% 46.64/46.89  thf('505', plain,
% 46.64/46.89      ((v1_funct_2 @ 
% 46.64/46.89        (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89         (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['502', '503', '504'])).
% 46.64/46.89  thf('506', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('507', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('508', plain,
% 46.64/46.89      ((v1_funct_2 @ 
% 46.64/46.89        (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['505', '506', '507'])).
% 46.64/46.89  thf('509', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('510', plain,
% 46.64/46.89      ((v1_funct_2 @ 
% 46.64/46.89        (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89         (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89        (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['508', '509'])).
% 46.64/46.89  thf('511', plain,
% 46.64/46.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 46.64/46.89        | ((k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89            (k2_funct_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['499', '510'])).
% 46.64/46.89  thf('512', plain,
% 46.64/46.89      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ 
% 46.64/46.89          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 46.64/46.89           (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89          k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['288', '477', '478'])).
% 46.64/46.89  thf('513', plain,
% 46.64/46.89      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0 @ 
% 46.64/46.89           k1_xboole_0)
% 46.64/46.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['511', '512'])).
% 46.64/46.89  thf('514', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['9', '10'])).
% 46.64/46.89  thf('515', plain,
% 46.64/46.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 46.64/46.89         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 46.64/46.89          | ~ (v1_funct_1 @ X26)
% 46.64/46.89          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 46.64/46.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['277'])).
% 46.64/46.89  thf('516', plain,
% 46.64/46.89      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 46.64/46.89           sk_C))),
% 46.64/46.89      inference('sup-', [status(thm)], ['514', '515'])).
% 46.64/46.89  thf('517', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['17', '18'])).
% 46.64/46.89  thf('518', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('519', plain,
% 46.64/46.89      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['516', '517', '518'])).
% 46.64/46.89  thf('520', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('521', plain,
% 46.64/46.89      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_C @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['519', '520'])).
% 46.64/46.89  thf('522', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('523', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('524', plain,
% 46.64/46.89      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0 @ 
% 46.64/46.89        k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['521', '522', '523'])).
% 46.64/46.89  thf('525', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['513', '524'])).
% 46.64/46.89  thf('526', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['513', '524'])).
% 46.64/46.89  thf('527', plain,
% 46.64/46.89      (~ (r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ 
% 46.64/46.89          (k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89          k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['479', '525', '526'])).
% 46.64/46.89  thf('528', plain,
% 46.64/46.89      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 46.64/46.89         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['92', '269', '270', '271', '272'])).
% 46.64/46.89  thf('529', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('530', plain,
% 46.64/46.89      (((k2_tops_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))
% 46.64/46.89         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['528', '529'])).
% 46.64/46.89  thf('531', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('532', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('533', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('534', plain,
% 46.64/46.89      (((k2_tops_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 46.64/46.89         (k2_funct_1 @ k1_xboole_0))
% 46.64/46.89         = (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['530', '531', '532', '533'])).
% 46.64/46.89  thf('535', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 46.64/46.89  thf('536', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('537', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['535', '536'])).
% 46.64/46.89  thf('538', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('539', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('540', plain,
% 46.64/46.89      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['537', '538', '539'])).
% 46.64/46.89  thf('541', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('542', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((m1_subset_1 @ X33 @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('543', plain,
% 46.64/46.89      (((m1_subset_1 @ sk_C @ 
% 46.64/46.89         (k1_zfmisc_1 @ 
% 46.64/46.89          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['541', '542'])).
% 46.64/46.89  thf('544', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('545', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('546', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ 
% 46.64/46.89         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 46.64/46.89      inference('demod', [status(thm)], ['543', '544', '545'])).
% 46.64/46.89  thf('547', plain,
% 46.64/46.89      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 46.64/46.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 46.64/46.89          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 46.64/46.89          | ~ (v1_funct_1 @ X23)
% 46.64/46.89          | ~ (v1_funct_1 @ X26)
% 46.64/46.89          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 46.64/46.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 46.64/46.89          | ((X23) = (X26))
% 46.64/46.89          | ~ (r2_funct_2 @ X24 @ X25 @ X23 @ X26))),
% 46.64/46.89      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 46.64/46.89  thf('548', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 46.64/46.89             X0)
% 46.64/46.89          | ((sk_C) = (X0))
% 46.64/46.89          | ~ (m1_subset_1 @ X0 @ 
% 46.64/46.89               (k1_zfmisc_1 @ 
% 46.64/46.89                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 46.64/46.89          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['546', '547'])).
% 46.64/46.89  thf('549', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('550', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('551', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('552', plain,
% 46.64/46.89      (((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['550', '551'])).
% 46.64/46.89  thf('553', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('554', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('555', plain,
% 46.64/46.89      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['552', '553', '554'])).
% 46.64/46.89  thf('556', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 46.64/46.89             X0)
% 46.64/46.89          | ((sk_C) = (X0))
% 46.64/46.89          | ~ (m1_subset_1 @ X0 @ 
% 46.64/46.89               (k1_zfmisc_1 @ 
% 46.64/46.89                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 46.64/46.89          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89          | ~ (v1_funct_1 @ X0))),
% 46.64/46.89      inference('demod', [status(thm)], ['548', '549', '555'])).
% 46.64/46.89  thf('557', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('558', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('559', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('560', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('561', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('562', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('563', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('564', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('565', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (r2_funct_2 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0 @ 
% 46.64/46.89             k1_xboole_0 @ X0)
% 46.64/46.89          | ((k1_xboole_0) = (X0))
% 46.64/46.89          | ~ (m1_subset_1 @ X0 @ 
% 46.64/46.89               (k1_zfmisc_1 @ 
% 46.64/46.89                (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 46.64/46.89          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0))),
% 46.64/46.89      inference('demod', [status(thm)],
% 46.64/46.89                ['556', '557', '558', '559', '560', '561', '562', '563', '564'])).
% 46.64/46.89  thf('566', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))
% 46.64/46.89        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89             (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 46.64/46.89        | ((k1_xboole_0) = (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))
% 46.64/46.89        | ~ (r2_funct_2 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0 @ 
% 46.64/46.89             k1_xboole_0 @ (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['540', '565'])).
% 46.64/46.89  thf('567', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('568', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 46.64/46.89      inference('simplify', [status(thm)], ['262'])).
% 46.64/46.89  thf('569', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('570', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('571', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89           (k1_zfmisc_1 @ 
% 46.64/46.89            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['185'])).
% 46.64/46.89  thf('572', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['570', '571'])).
% 46.64/46.89  thf('573', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['572'])).
% 46.64/46.89  thf('574', plain,
% 46.64/46.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 46.64/46.89         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 46.64/46.89          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 46.64/46.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 46.64/46.89  thf('575', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89              (k2_funct_1 @ X0)) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['573', '574'])).
% 46.64/46.89  thf('576', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('577', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('578', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('579', plain,
% 46.64/46.89      (![X5 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X5)
% 46.64/46.89          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 46.64/46.89          | ~ (v1_funct_1 @ X5)
% 46.64/46.89          | ~ (v1_relat_1 @ X5))),
% 46.64/46.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 46.64/46.89  thf('580', plain,
% 46.64/46.89      (![X33 : $i]:
% 46.64/46.89         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 46.64/46.89          | ~ (v1_funct_1 @ X33)
% 46.64/46.89          | ~ (v1_relat_1 @ X33))),
% 46.64/46.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 46.64/46.89  thf('581', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['579', '580'])).
% 46.64/46.89  thf('582', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['578', '581'])).
% 46.64/46.89  thf('583', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['582'])).
% 46.64/46.89  thf('584', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['577', '583'])).
% 46.64/46.89  thf('585', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['584'])).
% 46.64/46.89  thf('586', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0))),
% 46.64/46.89      inference('sup+', [status(thm)], ['576', '585'])).
% 46.64/46.89  thf('587', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['586'])).
% 46.64/46.89  thf('588', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['572'])).
% 46.64/46.89  thf('589', plain,
% 46.64/46.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X30)
% 46.64/46.89          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ X30))
% 46.64/46.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 46.64/46.89          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 46.64/46.89          | ~ (v1_funct_1 @ X30))),
% 46.64/46.89      inference('cnf', [status(esa)], [t31_funct_2])).
% 46.64/46.89  thf('590', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89               (k1_relat_1 @ X0))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['588', '589'])).
% 46.64/46.89  thf('591', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['587', '590'])).
% 46.64/46.89  thf('592', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['591'])).
% 46.64/46.89  thf('593', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['575', '592'])).
% 46.64/46.89  thf('594', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['593'])).
% 46.64/46.89  thf('595', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['569', '594'])).
% 46.64/46.89  thf('596', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['595'])).
% 46.64/46.89  thf('597', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 46.64/46.89        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['568', '596'])).
% 46.64/46.89  thf('598', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('599', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('600', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('601', plain,
% 46.64/46.89      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 46.64/46.89        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 46.64/46.89      inference('demod', [status(thm)], ['597', '598', '599', '600'])).
% 46.64/46.89  thf('602', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['567', '601'])).
% 46.64/46.89  thf('603', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('604', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('605', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('606', plain,
% 46.64/46.89      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 46.64/46.89        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 46.64/46.89      inference('demod', [status(thm)], ['602', '603', '604', '605'])).
% 46.64/46.89  thf('607', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['606'])).
% 46.64/46.89  thf('608', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('609', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['607', '608'])).
% 46.64/46.89  thf('610', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('611', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('612', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['148'])).
% 46.64/46.89  thf('613', plain,
% 46.64/46.89      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['611', '612'])).
% 46.64/46.89  thf('614', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('615', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('616', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('617', plain,
% 46.64/46.89      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['613', '614', '615', '616'])).
% 46.64/46.89  thf('618', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('619', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['617', '618'])).
% 46.64/46.89  thf('620', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('sup+', [status(thm)], ['66', '67'])).
% 46.64/46.89  thf('621', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['113'])).
% 46.64/46.89  thf('622', plain,
% 46.64/46.89      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['620', '621'])).
% 46.64/46.89  thf('623', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('624', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('625', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('626', plain,
% 46.64/46.89      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['622', '623', '624', '625'])).
% 46.64/46.89  thf('627', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 46.64/46.89        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('demod', [status(thm)], ['619', '626'])).
% 46.64/46.89  thf('628', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C)
% 46.64/46.89        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['610', '627'])).
% 46.64/46.89  thf('629', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('630', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('631', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('632', plain,
% 46.64/46.89      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['628', '629', '630', '631'])).
% 46.64/46.89  thf('633', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('634', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('635', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('636', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('637', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['584'])).
% 46.64/46.89  thf('638', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['636', '637'])).
% 46.64/46.89  thf('639', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['635', '638'])).
% 46.64/46.89  thf('640', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['639'])).
% 46.64/46.89  thf('641', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['634', '640'])).
% 46.64/46.89  thf('642', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['641'])).
% 46.64/46.89  thf('643', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['633', '642'])).
% 46.64/46.89  thf('644', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['643'])).
% 46.64/46.89  thf('645', plain,
% 46.64/46.89      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89         (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['632', '644'])).
% 46.64/46.89  thf('646', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('647', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('648', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('649', plain,
% 46.64/46.89      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['645', '646', '647', '648'])).
% 46.64/46.89  thf('650', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('651', plain,
% 46.64/46.89      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 46.64/46.89        (k1_relat_1 @ sk_C) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['649', '650'])).
% 46.64/46.89  thf('652', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('653', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('654', plain,
% 46.64/46.89      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 46.64/46.89        (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['651', '652', '653'])).
% 46.64/46.89  thf('655', plain,
% 46.64/46.89      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 46.64/46.89      inference('demod', [status(thm)], ['265', '266', '267', '268'])).
% 46.64/46.89  thf('656', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('657', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('658', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('659', plain,
% 46.64/46.89      (![X6 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X6)
% 46.64/46.89          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 46.64/46.89          | ~ (v1_funct_1 @ X6)
% 46.64/46.89          | ~ (v1_relat_1 @ X6))),
% 46.64/46.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 46.64/46.89  thf('660', plain,
% 46.64/46.89      (![X4 : $i]:
% 46.64/46.89         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 46.64/46.89          | ~ (v2_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_funct_1 @ X4)
% 46.64/46.89          | ~ (v1_relat_1 @ X4))),
% 46.64/46.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 46.64/46.89  thf('661', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89             (k1_relat_1 @ X0)))),
% 46.64/46.89      inference('simplify', [status(thm)], ['586'])).
% 46.64/46.89  thf('662', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 46.64/46.89             (k1_zfmisc_1 @ 
% 46.64/46.89              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['572'])).
% 46.64/46.89  thf('663', plain,
% 46.64/46.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 46.64/46.89         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 46.64/46.89          | ~ (v1_funct_1 @ X26)
% 46.64/46.89          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 46.64/46.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 46.64/46.89      inference('simplify', [status(thm)], ['277'])).
% 46.64/46.89  thf('664', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 46.64/46.89               (k1_relat_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89             (k2_funct_1 @ X0) @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['662', '663'])).
% 46.64/46.89  thf('665', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89             (k2_funct_1 @ X0) @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['661', '664'])).
% 46.64/46.89  thf('666', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89             (k2_funct_1 @ X0) @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['665'])).
% 46.64/46.89  thf('667', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89             (k2_funct_1 @ X0) @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['660', '666'])).
% 46.64/46.89  thf('668', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((r2_funct_2 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 46.64/46.89           (k2_funct_1 @ X0) @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['667'])).
% 46.64/46.89  thf('669', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 46.64/46.89      inference('sup+', [status(thm)], ['659', '668'])).
% 46.64/46.89  thf('670', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['658', '669'])).
% 46.64/46.89  thf('671', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['670'])).
% 46.64/46.89  thf('672', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['657', '671'])).
% 46.64/46.89  thf('673', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['672'])).
% 46.64/46.89  thf('674', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         (~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | (r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89             (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 46.64/46.89      inference('sup-', [status(thm)], ['656', '673'])).
% 46.64/46.89  thf('675', plain,
% 46.64/46.89      (![X0 : $i]:
% 46.64/46.89         ((r2_funct_2 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 46.64/46.89           (k1_relat_1 @ (k2_funct_1 @ X0)) @ X0 @ 
% 46.64/46.89           (k2_funct_1 @ (k2_funct_1 @ X0)))
% 46.64/46.89          | ~ (v2_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_funct_1 @ X0)
% 46.64/46.89          | ~ (v1_relat_1 @ X0))),
% 46.64/46.89      inference('simplify', [status(thm)], ['674'])).
% 46.64/46.89  thf('676', plain,
% 46.64/46.89      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ 
% 46.64/46.89         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_C @ 
% 46.64/46.89         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 46.64/46.89        | ~ (v1_relat_1 @ sk_C)
% 46.64/46.89        | ~ (v1_funct_1 @ sk_C)
% 46.64/46.89        | ~ (v2_funct_1 @ sk_C))),
% 46.64/46.89      inference('sup+', [status(thm)], ['655', '675'])).
% 46.64/46.89  thf('677', plain,
% 46.64/46.89      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 46.64/46.89      inference('demod', [status(thm)], ['628', '629', '630', '631'])).
% 46.64/46.89  thf('678', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['275', '282', '283', '284', '285'])).
% 46.64/46.89  thf('679', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['677', '678'])).
% 46.64/46.89  thf('680', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('681', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('682', plain, ((v2_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('683', plain,
% 46.64/46.89      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ k1_xboole_0 @ sk_C @ 
% 46.64/46.89        (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 46.64/46.89      inference('demod', [status(thm)], ['676', '679', '680', '681', '682'])).
% 46.64/46.89  thf('684', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('685', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('686', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('687', plain,
% 46.64/46.89      ((r2_funct_2 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0 @ k1_xboole_0 @ 
% 46.64/46.89        (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['683', '684', '685', '686'])).
% 46.64/46.89  thf('688', plain,
% 46.64/46.89      (((k1_xboole_0) = (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['566', '609', '654', '687'])).
% 46.64/46.89  thf('689', plain,
% 46.64/46.89      (((k2_tops_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 46.64/46.89         (k2_funct_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['534', '688'])).
% 46.64/46.89  thf('690', plain,
% 46.64/46.89      ((m1_subset_1 @ sk_C @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['442', '443'])).
% 46.64/46.89  thf('691', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('692', plain,
% 46.64/46.89      ((m1_subset_1 @ k1_xboole_0 @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['690', '691'])).
% 46.64/46.89  thf('693', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['513', '524'])).
% 46.64/46.89  thf('694', plain,
% 46.64/46.89      ((m1_subset_1 @ k1_xboole_0 @ 
% 46.64/46.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 46.64/46.89      inference('demod', [status(thm)], ['692', '693'])).
% 46.64/46.89  thf('695', plain,
% 46.64/46.89      (![X27 : $i, X28 : $i]:
% 46.64/46.89         (~ (v1_funct_2 @ X28 @ k1_xboole_0 @ X27)
% 46.64/46.89          | (v1_partfun1 @ X28 @ k1_xboole_0)
% 46.64/46.89          | ~ (m1_subset_1 @ X28 @ 
% 46.64/46.89               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X27)))
% 46.64/46.89          | ~ (v1_funct_1 @ X28))),
% 46.64/46.89      inference('simplify', [status(thm)], ['339'])).
% 46.64/46.89  thf('696', plain,
% 46.64/46.89      ((~ (v1_funct_1 @ k1_xboole_0)
% 46.64/46.89        | (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 46.64/46.89        | ~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 46.64/46.89      inference('sup-', [status(thm)], ['694', '695'])).
% 46.64/46.89  thf('697', plain, ((v1_funct_1 @ sk_C)),
% 46.64/46.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.64/46.89  thf('698', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('699', plain, ((v1_funct_1 @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['697', '698'])).
% 46.64/46.89  thf('700', plain, ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['447', '448'])).
% 46.64/46.89  thf('701', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('702', plain,
% 46.64/46.89      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['700', '701'])).
% 46.64/46.89  thf('703', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['513', '524'])).
% 46.64/46.89  thf('704', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['702', '703'])).
% 46.64/46.89  thf('705', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['696', '699', '704'])).
% 46.64/46.89  thf('706', plain,
% 46.64/46.89      (![X21 : $i, X22 : $i]:
% 46.64/46.89         (~ (v1_partfun1 @ X22 @ X21)
% 46.64/46.89          | ((k1_relat_1 @ X22) = (X21))
% 46.64/46.89          | ~ (v4_relat_1 @ X22 @ X21)
% 46.64/46.89          | ~ (v1_relat_1 @ X22))),
% 46.64/46.89      inference('cnf', [status(esa)], [d4_partfun1])).
% 46.64/46.89  thf('707', plain,
% 46.64/46.89      ((~ (v1_relat_1 @ k1_xboole_0)
% 46.64/46.89        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 46.64/46.89        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 46.64/46.89      inference('sup-', [status(thm)], ['705', '706'])).
% 46.64/46.89  thf('708', plain, ((v1_relat_1 @ sk_C)),
% 46.64/46.89      inference('demod', [status(thm)], ['48', '49'])).
% 46.64/46.89  thf('709', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('710', plain, ((v1_relat_1 @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['708', '709'])).
% 46.64/46.89  thf('711', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 46.64/46.89      inference('sup-', [status(thm)], ['51', '52'])).
% 46.64/46.89  thf('712', plain, (((sk_C) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 46.64/46.89  thf('713', plain, ((v4_relat_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 46.64/46.89      inference('demod', [status(thm)], ['711', '712'])).
% 46.64/46.89  thf('714', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['513', '524'])).
% 46.64/46.89  thf('715', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['713', '714'])).
% 46.64/46.89  thf('716', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['707', '710', '715'])).
% 46.64/46.89  thf('717', plain,
% 46.64/46.89      (((k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ k1_xboole_0))
% 46.64/46.89         = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['689', '716'])).
% 46.64/46.89  thf('718', plain,
% 46.64/46.89      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0 @ 
% 46.64/46.89        k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['521', '522', '523'])).
% 46.64/46.89  thf('719', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 46.64/46.89      inference('demod', [status(thm)], ['513', '524'])).
% 46.64/46.89  thf('720', plain,
% 46.64/46.89      ((r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 46.64/46.89      inference('demod', [status(thm)], ['718', '719'])).
% 46.64/46.89  thf('721', plain, ($false),
% 46.64/46.89      inference('demod', [status(thm)], ['527', '717', '720'])).
% 46.64/46.89  
% 46.64/46.89  % SZS output end Refutation
% 46.64/46.89  
% 46.64/46.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
