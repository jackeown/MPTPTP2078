%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.plVPAoZ8tG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:13 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  354 (2370 expanded)
%              Number of leaves         :   53 ( 717 expanded)
%              Depth                    :   37
%              Number of atoms          : 3420 (52359 expanded)
%              Number of equality atoms :  177 (1491 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('3',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
        = ( k2_funct_1 @ X22 ) )
      | ( ( k5_relat_1 @ X21 @ X22 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X22 ) ) )
      | ( ( k2_relat_1 @ X21 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
        = ( k2_funct_1 @ X22 ) )
      | ( ( k5_relat_1 @ X21 @ X22 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X22 ) ) )
      | ( ( k2_relat_1 @ X21 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','32','37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('46',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('50',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('51',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relat_1 @ X36 )
       != X35 )
      | ( v1_partfun1 @ X36 @ X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('65',plain,(
    ! [X36: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v4_relat_1 @ X36 @ ( k1_relat_1 @ X36 ) )
      | ( v1_partfun1 @ X36 @ ( k1_relat_1 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('71',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('77',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('79',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72','77','78'])).

thf('80',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('89',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['19','44','53','58','86','87','88'])).

thf('90',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('92',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('93',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('95',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('96',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('97',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('99',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('100',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('101',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
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
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('116',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('118',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('119',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('120',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','136'])).

thf('138',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['93','137'])).

thf('139',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('141',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('148',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('152',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['151','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150','159'])).

thf('161',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('162',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('164',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('165',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('166',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','166'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('168',plain,(
    ! [X52: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('169',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('177',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('178',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['138','173','174','175','176','177'])).

thf('179',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['92','178'])).

thf('180',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('181',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('182',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('185',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('188',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','187'])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('191',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('195',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('196',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('197',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('198',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('200',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('206',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['198','203','204','205','206'])).

thf('208',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['195','207'])).

thf('209',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['194','211'])).

thf('213',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['193','213'])).

thf('215',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('216',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('217',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('218',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['216','221'])).

thf('223',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('226',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_relset_1 @ X54 @ X53 @ X55 )
       != X53 )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_tops_2 @ X54 @ X53 @ X55 )
        = ( k2_funct_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('227',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('230',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('232',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['227','228','229','230','231'])).

thf('233',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['224','233'])).

thf('235',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['215','234'])).

thf('236',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('239',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('240',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('241',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('243',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('244',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_relset_1 @ X54 @ X53 @ X55 )
       != X53 )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_tops_2 @ X54 @ X53 @ X55 )
        = ( k2_funct_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('246',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('248',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('249',plain,(
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('250',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('252',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('253',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('255',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('256',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['254','257'])).

thf('259',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('260',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('261',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['246','247','253','261'])).

thf('263',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('265',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['238','265'])).

thf('267',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('268',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('271',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['237','270'])).

thf('272',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['214','271'])).

thf('273',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('275',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( r2_funct_2 @ X40 @ X41 @ X42 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['273','279'])).

thf('281',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['272','283'])).

thf('285',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','284'])).

thf('286',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X52: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('289',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf(rc1_relset_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( v1_xboole_0 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('290',plain,(
    ! [X37: $i,X38: $i] :
      ( v1_xboole_0 @ ( sk_C @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('291',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('292',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('293',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('294',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('295',plain,(
    ! [X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['290','295'])).

thf('297',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['289','296','297'])).

thf('299',plain,(
    $false ),
    inference(demod,[status(thm)],['0','298'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.plVPAoZ8tG
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.82/2.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.82/2.07  % Solved by: fo/fo7.sh
% 1.82/2.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.07  % done 1902 iterations in 1.601s
% 1.82/2.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.82/2.07  % SZS output start Refutation
% 1.82/2.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.82/2.07  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.82/2.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.82/2.07  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.82/2.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.82/2.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.82/2.07  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.82/2.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.82/2.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.82/2.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.82/2.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.82/2.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.82/2.07  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.82/2.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.82/2.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.82/2.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.82/2.07  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.82/2.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.82/2.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.82/2.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.82/2.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.82/2.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.82/2.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.82/2.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.82/2.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.82/2.07  thf(sk_B_type, type, sk_B: $i).
% 1.82/2.07  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.82/2.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.82/2.07  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.82/2.07  thf(t64_tops_2, conjecture,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( l1_struct_0 @ A ) =>
% 1.82/2.07       ( ![B:$i]:
% 1.82/2.07         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.82/2.07           ( ![C:$i]:
% 1.82/2.07             ( ( ( v1_funct_1 @ C ) & 
% 1.82/2.07                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.82/2.07                 ( m1_subset_1 @
% 1.82/2.07                   C @ 
% 1.82/2.07                   ( k1_zfmisc_1 @
% 1.82/2.07                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.82/2.07               ( ( ( ( k2_relset_1 @
% 1.82/2.07                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.82/2.07                     ( k2_struct_0 @ B ) ) & 
% 1.82/2.07                   ( v2_funct_1 @ C ) ) =>
% 1.82/2.07                 ( r2_funct_2 @
% 1.82/2.07                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.82/2.07                   ( k2_tops_2 @
% 1.82/2.07                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.82/2.07                     ( k2_tops_2 @
% 1.82/2.07                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.82/2.07                   C ) ) ) ) ) ) ))).
% 1.82/2.07  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.07    (~( ![A:$i]:
% 1.82/2.07        ( ( l1_struct_0 @ A ) =>
% 1.82/2.07          ( ![B:$i]:
% 1.82/2.07            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.82/2.07              ( ![C:$i]:
% 1.82/2.07                ( ( ( v1_funct_1 @ C ) & 
% 1.82/2.07                    ( v1_funct_2 @
% 1.82/2.07                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.82/2.07                    ( m1_subset_1 @
% 1.82/2.07                      C @ 
% 1.82/2.07                      ( k1_zfmisc_1 @
% 1.82/2.07                        ( k2_zfmisc_1 @
% 1.82/2.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.82/2.07                  ( ( ( ( k2_relset_1 @
% 1.82/2.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.82/2.07                        ( k2_struct_0 @ B ) ) & 
% 1.82/2.07                      ( v2_funct_1 @ C ) ) =>
% 1.82/2.07                    ( r2_funct_2 @
% 1.82/2.07                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.82/2.07                      ( k2_tops_2 @
% 1.82/2.07                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.82/2.07                        ( k2_tops_2 @
% 1.82/2.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.82/2.07                      C ) ) ) ) ) ) ) )),
% 1.82/2.07    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 1.82/2.07  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(d3_struct_0, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.82/2.07  thf('1', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf(fc6_funct_1, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.82/2.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.82/2.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.82/2.07         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.82/2.07  thf('2', plain,
% 1.82/2.07      (![X17 : $i]:
% 1.82/2.07         ((v2_funct_1 @ (k2_funct_1 @ X17))
% 1.82/2.07          | ~ (v2_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_relat_1 @ X17))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.82/2.07  thf('3', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('4', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(t35_funct_2, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.82/2.07         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.82/2.07           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.82/2.07             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.82/2.07  thf('5', plain,
% 1.82/2.07      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.82/2.07         (((X47) = (k1_xboole_0))
% 1.82/2.07          | ~ (v1_funct_1 @ X48)
% 1.82/2.07          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 1.82/2.07          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 1.82/2.07          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 1.82/2.07          | ~ (v2_funct_1 @ X48)
% 1.82/2.07          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 1.82/2.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.82/2.07  thf('6', plain,
% 1.82/2.07      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07          != (u1_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.82/2.07        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['4', '5'])).
% 1.82/2.07  thf('7', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('8', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('9', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('10', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('11', plain,
% 1.82/2.07      ((((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B))
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 1.82/2.07  thf('12', plain,
% 1.82/2.07      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B)
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 1.82/2.07      inference('sup-', [status(thm)], ['3', '11'])).
% 1.82/2.07  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('14', plain,
% 1.82/2.07      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 1.82/2.07      inference('demod', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('15', plain,
% 1.82/2.07      ((((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('simplify', [status(thm)], ['14'])).
% 1.82/2.07  thf(t64_funct_1, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.82/2.07       ( ![B:$i]:
% 1.82/2.07         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.82/2.07           ( ( ( v2_funct_1 @ A ) & 
% 1.82/2.07               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.82/2.07               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.82/2.07             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.82/2.07  thf('16', plain,
% 1.82/2.07      (![X21 : $i, X22 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X21)
% 1.82/2.07          | ~ (v1_funct_1 @ X21)
% 1.82/2.07          | ((X21) = (k2_funct_1 @ X22))
% 1.82/2.07          | ((k5_relat_1 @ X21 @ X22) != (k6_relat_1 @ (k2_relat_1 @ X22)))
% 1.82/2.07          | ((k2_relat_1 @ X21) != (k1_relat_1 @ X22))
% 1.82/2.07          | ~ (v2_funct_1 @ X22)
% 1.82/2.07          | ~ (v1_funct_1 @ X22)
% 1.82/2.07          | ~ (v1_relat_1 @ X22))),
% 1.82/2.07      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.82/2.07  thf(redefinition_k6_partfun1, axiom,
% 1.82/2.07    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.82/2.07  thf('17', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.82/2.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.82/2.07  thf('18', plain,
% 1.82/2.07      (![X21 : $i, X22 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X21)
% 1.82/2.07          | ~ (v1_funct_1 @ X21)
% 1.82/2.07          | ((X21) = (k2_funct_1 @ X22))
% 1.82/2.07          | ((k5_relat_1 @ X21 @ X22) != (k6_partfun1 @ (k2_relat_1 @ X22)))
% 1.82/2.07          | ((k2_relat_1 @ X21) != (k1_relat_1 @ X22))
% 1.82/2.07          | ~ (v2_funct_1 @ X22)
% 1.82/2.07          | ~ (v1_funct_1 @ X22)
% 1.82/2.07          | ~ (v1_relat_1 @ X22))),
% 1.82/2.07      inference('demod', [status(thm)], ['16', '17'])).
% 1.82/2.07  thf('19', plain,
% 1.82/2.07      ((((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((k2_relat_1 @ sk_C_1) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_relat_1 @ sk_C_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['15', '18'])).
% 1.82/2.07  thf('20', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('21', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('22', plain,
% 1.82/2.07      (((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07         (k1_zfmisc_1 @ 
% 1.82/2.07          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['20', '21'])).
% 1.82/2.07  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('24', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['22', '23'])).
% 1.82/2.07  thf(t31_funct_2, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.07       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.82/2.07         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.82/2.07           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.82/2.07           ( m1_subset_1 @
% 1.82/2.07             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.82/2.07  thf('25', plain,
% 1.82/2.07      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X44)
% 1.82/2.07          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 1.82/2.07          | (m1_subset_1 @ (k2_funct_1 @ X44) @ 
% 1.82/2.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.82/2.07          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.82/2.07          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 1.82/2.07          | ~ (v1_funct_1 @ X44))),
% 1.82/2.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.82/2.07  thf('26', plain,
% 1.82/2.07      ((~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.82/2.07           (k1_zfmisc_1 @ 
% 1.82/2.07            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.82/2.07        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07            != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['24', '25'])).
% 1.82/2.07  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('28', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('29', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('30', plain,
% 1.82/2.07      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['28', '29'])).
% 1.82/2.07  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('32', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['30', '31'])).
% 1.82/2.07  thf('33', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('34', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('35', plain,
% 1.82/2.07      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07          = (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['33', '34'])).
% 1.82/2.07  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('37', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['35', '36'])).
% 1.82/2.07  thf('38', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('39', plain,
% 1.82/2.07      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.82/2.07         (k1_zfmisc_1 @ 
% 1.82/2.07          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.82/2.07        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 1.82/2.07      inference('demod', [status(thm)], ['26', '27', '32', '37', '38'])).
% 1.82/2.07  thf('40', plain,
% 1.82/2.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.82/2.07      inference('simplify', [status(thm)], ['39'])).
% 1.82/2.07  thf(cc2_relat_1, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( v1_relat_1 @ A ) =>
% 1.82/2.07       ( ![B:$i]:
% 1.82/2.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.82/2.07  thf('41', plain,
% 1.82/2.07      (![X7 : $i, X8 : $i]:
% 1.82/2.07         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.82/2.07          | (v1_relat_1 @ X7)
% 1.82/2.07          | ~ (v1_relat_1 @ X8))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.82/2.07  thf('42', plain,
% 1.82/2.07      ((~ (v1_relat_1 @ 
% 1.82/2.07           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 1.82/2.07        | (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['40', '41'])).
% 1.82/2.07  thf(fc6_relat_1, axiom,
% 1.82/2.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.82/2.07  thf('43', plain,
% 1.82/2.07      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.82/2.07  thf('44', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.07  thf('45', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['22', '23'])).
% 1.82/2.07  thf('46', plain,
% 1.82/2.07      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X44)
% 1.82/2.07          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 1.82/2.07          | (v1_funct_1 @ (k2_funct_1 @ X44))
% 1.82/2.07          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.82/2.07          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 1.82/2.07          | ~ (v1_funct_1 @ X44))),
% 1.82/2.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.82/2.07  thf('47', plain,
% 1.82/2.07      ((~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07            != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['45', '46'])).
% 1.82/2.07  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('49', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['30', '31'])).
% 1.82/2.07  thf('50', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['35', '36'])).
% 1.82/2.07  thf('51', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('52', plain,
% 1.82/2.07      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 1.82/2.07      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 1.82/2.07  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.07  thf('54', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(redefinition_k2_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.82/2.07  thf('55', plain,
% 1.82/2.07      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.82/2.07         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.82/2.07          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.82/2.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.82/2.07  thf('56', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_relat_1 @ sk_C_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['54', '55'])).
% 1.82/2.07  thf('57', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('58', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['56', '57'])).
% 1.82/2.07  thf('59', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.07  thf(t55_funct_1, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.82/2.07       ( ( v2_funct_1 @ A ) =>
% 1.82/2.07         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.82/2.07           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.82/2.07  thf('60', plain,
% 1.82/2.07      (![X20 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X20)
% 1.82/2.07          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.82/2.07          | ~ (v1_funct_1 @ X20)
% 1.82/2.07          | ~ (v1_relat_1 @ X20))),
% 1.82/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.82/2.07  thf(t3_funct_2, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.82/2.07       ( ( v1_funct_1 @ A ) & 
% 1.82/2.07         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.82/2.07         ( m1_subset_1 @
% 1.82/2.07           A @ 
% 1.82/2.07           ( k1_zfmisc_1 @
% 1.82/2.07             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.82/2.07  thf('61', plain,
% 1.82/2.07      (![X50 : $i]:
% 1.82/2.07         ((m1_subset_1 @ X50 @ 
% 1.82/2.07           (k1_zfmisc_1 @ 
% 1.82/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.82/2.07          | ~ (v1_funct_1 @ X50)
% 1.82/2.07          | ~ (v1_relat_1 @ X50))),
% 1.82/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.82/2.07  thf(cc2_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.82/2.07  thf('62', plain,
% 1.82/2.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.82/2.07         ((v4_relat_1 @ X23 @ X24)
% 1.82/2.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.82/2.07  thf('63', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['61', '62'])).
% 1.82/2.07  thf(d4_partfun1, axiom,
% 1.82/2.07    (![A:$i,B:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.82/2.07       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.82/2.07  thf('64', plain,
% 1.82/2.07      (![X35 : $i, X36 : $i]:
% 1.82/2.07         (((k1_relat_1 @ X36) != (X35))
% 1.82/2.07          | (v1_partfun1 @ X36 @ X35)
% 1.82/2.07          | ~ (v4_relat_1 @ X36 @ X35)
% 1.82/2.07          | ~ (v1_relat_1 @ X36))),
% 1.82/2.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.82/2.07  thf('65', plain,
% 1.82/2.07      (![X36 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X36)
% 1.82/2.07          | ~ (v4_relat_1 @ X36 @ (k1_relat_1 @ X36))
% 1.82/2.07          | (v1_partfun1 @ X36 @ (k1_relat_1 @ X36)))),
% 1.82/2.07      inference('simplify', [status(thm)], ['64'])).
% 1.82/2.07  thf('66', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('sup-', [status(thm)], ['63', '65'])).
% 1.82/2.07  thf('67', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['66'])).
% 1.82/2.07  thf('68', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['60', '67'])).
% 1.82/2.07  thf('69', plain,
% 1.82/2.07      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_relat_1 @ sk_C_1)
% 1.82/2.07        | (v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['59', '68'])).
% 1.82/2.07  thf('70', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.07  thf('71', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('72', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('73', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('74', plain,
% 1.82/2.07      (![X7 : $i, X8 : $i]:
% 1.82/2.07         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.82/2.07          | (v1_relat_1 @ X7)
% 1.82/2.07          | ~ (v1_relat_1 @ X8))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.82/2.07  thf('75', plain,
% 1.82/2.07      ((~ (v1_relat_1 @ 
% 1.82/2.07           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.82/2.07        | (v1_relat_1 @ sk_C_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['73', '74'])).
% 1.82/2.07  thf('76', plain,
% 1.82/2.07      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.82/2.07  thf('77', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.07  thf('78', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['56', '57'])).
% 1.82/2.07  thf('79', plain,
% 1.82/2.07      ((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['69', '70', '71', '72', '77', '78'])).
% 1.82/2.07  thf('80', plain,
% 1.82/2.07      (![X35 : $i, X36 : $i]:
% 1.82/2.07         (~ (v1_partfun1 @ X36 @ X35)
% 1.82/2.07          | ((k1_relat_1 @ X36) = (X35))
% 1.82/2.07          | ~ (v4_relat_1 @ X36 @ X35)
% 1.82/2.07          | ~ (v1_relat_1 @ X36))),
% 1.82/2.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.82/2.07  thf('81', plain,
% 1.82/2.07      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['79', '80'])).
% 1.82/2.07  thf('82', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.07  thf('83', plain,
% 1.82/2.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.82/2.07      inference('simplify', [status(thm)], ['39'])).
% 1.82/2.07  thf('84', plain,
% 1.82/2.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.82/2.07         ((v4_relat_1 @ X23 @ X24)
% 1.82/2.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.82/2.07  thf('85', plain,
% 1.82/2.07      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup-', [status(thm)], ['83', '84'])).
% 1.82/2.07  thf('86', plain,
% 1.82/2.07      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['81', '82', '85'])).
% 1.82/2.07  thf('87', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('88', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.07  thf('89', plain,
% 1.82/2.07      ((((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.07      inference('demod', [status(thm)],
% 1.82/2.07                ['19', '44', '53', '58', '86', '87', '88'])).
% 1.82/2.07  thf('90', plain,
% 1.82/2.07      ((((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 1.82/2.07      inference('simplify', [status(thm)], ['89'])).
% 1.82/2.07  thf('91', plain,
% 1.82/2.07      (![X17 : $i]:
% 1.82/2.07         ((v2_funct_1 @ (k2_funct_1 @ X17))
% 1.82/2.07          | ~ (v2_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_relat_1 @ X17))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.82/2.07  thf('92', plain,
% 1.82/2.07      (![X20 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X20)
% 1.82/2.07          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.82/2.07          | ~ (v1_funct_1 @ X20)
% 1.82/2.07          | ~ (v1_relat_1 @ X20))),
% 1.82/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.82/2.07  thf('93', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.07  thf(dt_k2_funct_1, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.82/2.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.82/2.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.82/2.07  thf('94', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('95', plain,
% 1.82/2.07      (![X17 : $i]:
% 1.82/2.07         ((v2_funct_1 @ (k2_funct_1 @ X17))
% 1.82/2.07          | ~ (v2_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_relat_1 @ X17))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.82/2.07  thf('96', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('97', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('98', plain,
% 1.82/2.07      (![X20 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X20)
% 1.82/2.07          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 1.82/2.07          | ~ (v1_funct_1 @ X20)
% 1.82/2.07          | ~ (v1_relat_1 @ X20))),
% 1.82/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.82/2.07  thf('99', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('100', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('101', plain,
% 1.82/2.07      (![X20 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X20)
% 1.82/2.07          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.82/2.07          | ~ (v1_funct_1 @ X20)
% 1.82/2.07          | ~ (v1_relat_1 @ X20))),
% 1.82/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.82/2.07  thf('102', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['61', '62'])).
% 1.82/2.07  thf('103', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['101', '102'])).
% 1.82/2.07  thf('104', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['100', '103'])).
% 1.82/2.07  thf('105', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['104'])).
% 1.82/2.07  thf('106', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['99', '105'])).
% 1.82/2.07  thf('107', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['106'])).
% 1.82/2.07  thf('108', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['98', '107'])).
% 1.82/2.07  thf('109', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['97', '108'])).
% 1.82/2.07  thf('110', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['109'])).
% 1.82/2.07  thf('111', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['96', '110'])).
% 1.82/2.07  thf('112', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['111'])).
% 1.82/2.07  thf('113', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['95', '112'])).
% 1.82/2.07  thf('114', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['113'])).
% 1.82/2.07  thf('115', plain,
% 1.82/2.07      (![X17 : $i]:
% 1.82/2.07         ((v2_funct_1 @ (k2_funct_1 @ X17))
% 1.82/2.07          | ~ (v2_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_funct_1 @ X17)
% 1.82/2.07          | ~ (v1_relat_1 @ X17))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.82/2.07  thf('116', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('117', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('118', plain,
% 1.82/2.07      (![X20 : $i]:
% 1.82/2.07         (~ (v2_funct_1 @ X20)
% 1.82/2.07          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 1.82/2.07          | ~ (v1_funct_1 @ X20)
% 1.82/2.07          | ~ (v1_relat_1 @ X20))),
% 1.82/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.82/2.07  thf('119', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('120', plain,
% 1.82/2.07      (![X14 : $i]:
% 1.82/2.07         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 1.82/2.07          | ~ (v1_funct_1 @ X14)
% 1.82/2.07          | ~ (v1_relat_1 @ X14))),
% 1.82/2.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.82/2.07  thf('121', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['60', '67'])).
% 1.82/2.07  thf('122', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['120', '121'])).
% 1.82/2.07  thf('123', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['122'])).
% 1.82/2.07  thf('124', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['119', '123'])).
% 1.82/2.07  thf('125', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['124'])).
% 1.82/2.07  thf('126', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['118', '125'])).
% 1.82/2.07  thf('127', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['117', '126'])).
% 1.82/2.07  thf('128', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['127'])).
% 1.82/2.07  thf('129', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['116', '128'])).
% 1.82/2.07  thf('130', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['129'])).
% 1.82/2.07  thf('131', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['115', '130'])).
% 1.82/2.07  thf('132', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['131'])).
% 1.82/2.07  thf('133', plain,
% 1.82/2.07      (![X35 : $i, X36 : $i]:
% 1.82/2.07         (~ (v1_partfun1 @ X36 @ X35)
% 1.82/2.07          | ((k1_relat_1 @ X36) = (X35))
% 1.82/2.07          | ~ (v4_relat_1 @ X36 @ X35)
% 1.82/2.07          | ~ (v1_relat_1 @ X36))),
% 1.82/2.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.82/2.07  thf('134', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07          | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.82/2.07               (k1_relat_1 @ X0))
% 1.82/2.07          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07              = (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['132', '133'])).
% 1.82/2.07  thf('135', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07              = (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('sup-', [status(thm)], ['114', '134'])).
% 1.82/2.07  thf('136', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07              = (k1_relat_1 @ X0))
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v1_relat_1 @ X0))),
% 1.82/2.07      inference('simplify', [status(thm)], ['135'])).
% 1.82/2.07  thf('137', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.82/2.07          | ~ (v1_relat_1 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ X0)
% 1.82/2.07          | ~ (v2_funct_1 @ X0)
% 1.82/2.07          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.82/2.07              = (k1_relat_1 @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['94', '136'])).
% 1.82/2.07  thf('138', plain,
% 1.82/2.07      ((((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07          = (k1_relat_1 @ sk_C_1))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_relat_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['93', '137'])).
% 1.82/2.07  thf('139', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('140', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('141', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('142', plain,
% 1.82/2.07      (((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07         (k1_zfmisc_1 @ 
% 1.82/2.07          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.82/2.07      inference('sup+', [status(thm)], ['140', '141'])).
% 1.82/2.07  thf('143', plain, ((l1_struct_0 @ sk_A)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('144', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['142', '143'])).
% 1.82/2.07  thf('145', plain,
% 1.82/2.07      (((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07         (k1_zfmisc_1 @ 
% 1.82/2.07          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['139', '144'])).
% 1.82/2.07  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('147', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['145', '146'])).
% 1.82/2.07  thf(cc5_funct_2, axiom,
% 1.82/2.07    (![A:$i,B:$i]:
% 1.82/2.07     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.82/2.07       ( ![C:$i]:
% 1.82/2.07         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.82/2.07             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.82/2.07  thf('148', plain,
% 1.82/2.07      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.82/2.07         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.82/2.07          | (v1_partfun1 @ X32 @ X33)
% 1.82/2.07          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 1.82/2.07          | ~ (v1_funct_1 @ X32)
% 1.82/2.07          | (v1_xboole_0 @ X34))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.82/2.07  thf('149', plain,
% 1.82/2.07      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['147', '148'])).
% 1.82/2.07  thf('150', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('151', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('152', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('153', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('154', plain,
% 1.82/2.07      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.82/2.07      inference('sup+', [status(thm)], ['152', '153'])).
% 1.82/2.07  thf('155', plain, ((l1_struct_0 @ sk_A)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('156', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['154', '155'])).
% 1.82/2.07  thf('157', plain,
% 1.82/2.07      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup+', [status(thm)], ['151', '156'])).
% 1.82/2.07  thf('158', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('159', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['157', '158'])).
% 1.82/2.07  thf('160', plain,
% 1.82/2.07      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 1.82/2.07      inference('demod', [status(thm)], ['149', '150', '159'])).
% 1.82/2.07  thf('161', plain,
% 1.82/2.07      (![X35 : $i, X36 : $i]:
% 1.82/2.07         (~ (v1_partfun1 @ X36 @ X35)
% 1.82/2.07          | ((k1_relat_1 @ X36) = (X35))
% 1.82/2.07          | ~ (v4_relat_1 @ X36 @ X35)
% 1.82/2.07          | ~ (v1_relat_1 @ X36))),
% 1.82/2.07      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.82/2.07  thf('162', plain,
% 1.82/2.07      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v1_relat_1 @ sk_C_1)
% 1.82/2.07        | ~ (v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))
% 1.82/2.07        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['160', '161'])).
% 1.82/2.07  thf('163', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.07  thf('164', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['142', '143'])).
% 1.82/2.07  thf('165', plain,
% 1.82/2.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.82/2.07         ((v4_relat_1 @ X23 @ X24)
% 1.82/2.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.82/2.07  thf('166', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 1.82/2.07      inference('sup-', [status(thm)], ['164', '165'])).
% 1.82/2.07  thf('167', plain,
% 1.82/2.07      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 1.82/2.07      inference('demod', [status(thm)], ['162', '163', '166'])).
% 1.82/2.07  thf(fc5_struct_0, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.82/2.07       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.82/2.07  thf('168', plain,
% 1.82/2.07      (![X52 : $i]:
% 1.82/2.07         (~ (v1_xboole_0 @ (k2_struct_0 @ X52))
% 1.82/2.07          | ~ (l1_struct_0 @ X52)
% 1.82/2.07          | (v2_struct_0 @ X52))),
% 1.82/2.07      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.82/2.07  thf('169', plain,
% 1.82/2.07      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 1.82/2.07        | (v2_struct_0 @ sk_B)
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup-', [status(thm)], ['167', '168'])).
% 1.82/2.07  thf('170', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('171', plain,
% 1.82/2.07      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['169', '170'])).
% 1.82/2.07  thf('172', plain, (~ (v2_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('173', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.82/2.07      inference('clc', [status(thm)], ['171', '172'])).
% 1.82/2.07  thf('174', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('175', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('176', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.07  thf('177', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.07  thf('178', plain,
% 1.82/2.07      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07         = (k2_struct_0 @ sk_A))),
% 1.82/2.07      inference('demod', [status(thm)],
% 1.82/2.07                ['138', '173', '174', '175', '176', '177'])).
% 1.82/2.07  thf('179', plain,
% 1.82/2.07      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))
% 1.82/2.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['92', '178'])).
% 1.82/2.07  thf('180', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.07  thf('181', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.07      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.07  thf('182', plain,
% 1.82/2.07      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))
% 1.82/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.07      inference('demod', [status(thm)], ['179', '180', '181'])).
% 1.82/2.07  thf('183', plain,
% 1.82/2.07      ((~ (v1_relat_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['91', '182'])).
% 1.82/2.07  thf('184', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.07  thf('185', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('186', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('187', plain,
% 1.82/2.07      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))),
% 1.82/2.07      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 1.82/2.07  thf('188', plain,
% 1.82/2.07      ((((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07            != (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 1.82/2.07      inference('demod', [status(thm)], ['90', '187'])).
% 1.82/2.07  thf('189', plain,
% 1.82/2.07      ((~ (v1_relat_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07            != (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.07      inference('sup-', [status(thm)], ['2', '188'])).
% 1.82/2.07  thf('190', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.07  thf('191', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('192', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('193', plain,
% 1.82/2.07      ((((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07          != (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.07      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 1.82/2.07  thf('194', plain,
% 1.82/2.07      ((((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('simplify', [status(thm)], ['14'])).
% 1.82/2.07  thf('195', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('196', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['142', '143'])).
% 1.82/2.07  thf('197', plain,
% 1.82/2.07      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.82/2.07         (((X47) = (k1_xboole_0))
% 1.82/2.07          | ~ (v1_funct_1 @ X48)
% 1.82/2.07          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 1.82/2.07          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 1.82/2.07          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 1.82/2.07          | ~ (v2_funct_1 @ X48)
% 1.82/2.07          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 1.82/2.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.82/2.07  thf('198', plain,
% 1.82/2.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07          != (u1_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 1.82/2.07        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.82/2.07        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['196', '197'])).
% 1.82/2.07  thf('199', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('200', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('201', plain,
% 1.82/2.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07          = (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.82/2.07      inference('sup+', [status(thm)], ['199', '200'])).
% 1.82/2.07  thf('202', plain, ((l1_struct_0 @ sk_A)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('203', plain,
% 1.82/2.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['201', '202'])).
% 1.82/2.07  thf('204', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('205', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['154', '155'])).
% 1.82/2.07  thf('206', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('207', plain,
% 1.82/2.07      ((((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B))
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('demod', [status(thm)], ['198', '203', '204', '205', '206'])).
% 1.82/2.07  thf('208', plain,
% 1.82/2.07      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B)
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 1.82/2.07      inference('sup-', [status(thm)], ['195', '207'])).
% 1.82/2.07  thf('209', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('210', plain,
% 1.82/2.07      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 1.82/2.07      inference('demod', [status(thm)], ['208', '209'])).
% 1.82/2.07  thf('211', plain,
% 1.82/2.07      ((((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.07          = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('simplify', [status(thm)], ['210'])).
% 1.82/2.07  thf('212', plain,
% 1.82/2.07      ((((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07          = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['194', '211'])).
% 1.82/2.07  thf('213', plain,
% 1.82/2.07      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.82/2.07        | ((k6_partfun1 @ (u1_struct_0 @ sk_A))
% 1.82/2.07            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 1.82/2.07      inference('simplify', [status(thm)], ['212'])).
% 1.82/2.07  thf('214', plain,
% 1.82/2.07      ((((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.07        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.07      inference('clc', [status(thm)], ['193', '213'])).
% 1.82/2.07  thf('215', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('216', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('217', plain,
% 1.82/2.07      (![X51 : $i]:
% 1.82/2.07         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 1.82/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.07  thf('218', plain,
% 1.82/2.07      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.07          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 1.82/2.07          sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('219', plain,
% 1.82/2.07      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.07           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.07            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 1.82/2.07           sk_C_1)
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup-', [status(thm)], ['217', '218'])).
% 1.82/2.07  thf('220', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('221', plain,
% 1.82/2.07      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.07          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 1.82/2.07          sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['219', '220'])).
% 1.82/2.07  thf('222', plain,
% 1.82/2.07      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.07           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.07            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 1.82/2.07           sk_C_1)
% 1.82/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.07      inference('sup-', [status(thm)], ['216', '221'])).
% 1.82/2.07  thf('223', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('224', plain,
% 1.82/2.07      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.07          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 1.82/2.07          sk_C_1)),
% 1.82/2.07      inference('demod', [status(thm)], ['222', '223'])).
% 1.82/2.07  thf('225', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.07        (k1_zfmisc_1 @ 
% 1.82/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.82/2.07      inference('demod', [status(thm)], ['22', '23'])).
% 1.82/2.07  thf(d4_tops_2, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.82/2.07         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.82/2.07  thf('226', plain,
% 1.82/2.07      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.82/2.07         (((k2_relset_1 @ X54 @ X53 @ X55) != (X53))
% 1.82/2.07          | ~ (v2_funct_1 @ X55)
% 1.82/2.07          | ((k2_tops_2 @ X54 @ X53 @ X55) = (k2_funct_1 @ X55))
% 1.82/2.07          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 1.82/2.07          | ~ (v1_funct_2 @ X55 @ X54 @ X53)
% 1.82/2.07          | ~ (v1_funct_1 @ X55))),
% 1.82/2.07      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.82/2.07  thf('227', plain,
% 1.82/2.07      ((~ (v1_funct_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.82/2.07        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07            = (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.07        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07            != (k2_struct_0 @ sk_B)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['225', '226'])).
% 1.82/2.07  thf('228', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('229', plain,
% 1.82/2.07      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['30', '31'])).
% 1.82/2.07  thf('230', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('231', plain,
% 1.82/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07         = (k2_struct_0 @ sk_B))),
% 1.82/2.07      inference('demod', [status(thm)], ['35', '36'])).
% 1.82/2.07  thf('232', plain,
% 1.82/2.07      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.07          = (k2_funct_1 @ sk_C_1))
% 1.82/2.07        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 1.82/2.07      inference('demod', [status(thm)], ['227', '228', '229', '230', '231'])).
% 1.82/2.07  thf('233', plain,
% 1.82/2.07      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 1.82/2.08         = (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('simplify', [status(thm)], ['232'])).
% 1.82/2.08  thf('234', plain,
% 1.82/2.08      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.08          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.08           (k2_funct_1 @ sk_C_1)) @ 
% 1.82/2.08          sk_C_1)),
% 1.82/2.08      inference('demod', [status(thm)], ['224', '233'])).
% 1.82/2.08  thf('235', plain,
% 1.82/2.08      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.08           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.82/2.08            (k2_funct_1 @ sk_C_1)) @ 
% 1.82/2.08           sk_C_1)
% 1.82/2.08        | ~ (l1_struct_0 @ sk_A))),
% 1.82/2.08      inference('sup-', [status(thm)], ['215', '234'])).
% 1.82/2.08  thf('236', plain, ((l1_struct_0 @ sk_A)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('237', plain,
% 1.82/2.08      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.08          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.82/2.08           (k2_funct_1 @ sk_C_1)) @ 
% 1.82/2.08          sk_C_1)),
% 1.82/2.08      inference('demod', [status(thm)], ['235', '236'])).
% 1.82/2.08  thf('238', plain,
% 1.82/2.08      (![X17 : $i]:
% 1.82/2.08         ((v2_funct_1 @ (k2_funct_1 @ X17))
% 1.82/2.08          | ~ (v2_funct_1 @ X17)
% 1.82/2.08          | ~ (v1_funct_1 @ X17)
% 1.82/2.08          | ~ (v1_relat_1 @ X17))),
% 1.82/2.08      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.82/2.08  thf('239', plain,
% 1.82/2.08      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 1.82/2.08      inference('demod', [status(thm)], ['81', '82', '85'])).
% 1.82/2.08  thf('240', plain,
% 1.82/2.08      (![X50 : $i]:
% 1.82/2.08         ((m1_subset_1 @ X50 @ 
% 1.82/2.08           (k1_zfmisc_1 @ 
% 1.82/2.08            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.82/2.08          | ~ (v1_funct_1 @ X50)
% 1.82/2.08          | ~ (v1_relat_1 @ X50))),
% 1.82/2.08      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.82/2.08  thf('241', plain,
% 1.82/2.08      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.82/2.08         (k1_zfmisc_1 @ 
% 1.82/2.08          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08           (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 1.82/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.08      inference('sup+', [status(thm)], ['239', '240'])).
% 1.82/2.08  thf('242', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.08  thf('243', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.08  thf('244', plain,
% 1.82/2.08      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.82/2.08        (k1_zfmisc_1 @ 
% 1.82/2.08         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08          (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 1.82/2.08      inference('demod', [status(thm)], ['241', '242', '243'])).
% 1.82/2.08  thf('245', plain,
% 1.82/2.08      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.82/2.08         (((k2_relset_1 @ X54 @ X53 @ X55) != (X53))
% 1.82/2.08          | ~ (v2_funct_1 @ X55)
% 1.82/2.08          | ((k2_tops_2 @ X54 @ X53 @ X55) = (k2_funct_1 @ X55))
% 1.82/2.08          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 1.82/2.08          | ~ (v1_funct_2 @ X55 @ X54 @ X53)
% 1.82/2.08          | ~ (v1_funct_1 @ X55))),
% 1.82/2.08      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.82/2.08  thf('246', plain,
% 1.82/2.08      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08             (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.08        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08            (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08            = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.08        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08            (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08            != (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.08      inference('sup-', [status(thm)], ['244', '245'])).
% 1.82/2.08  thf('247', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.08  thf('248', plain,
% 1.82/2.08      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 1.82/2.08      inference('demod', [status(thm)], ['81', '82', '85'])).
% 1.82/2.08  thf('249', plain,
% 1.82/2.08      (![X50 : $i]:
% 1.82/2.08         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 1.82/2.08          | ~ (v1_funct_1 @ X50)
% 1.82/2.08          | ~ (v1_relat_1 @ X50))),
% 1.82/2.08      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.82/2.08  thf('250', plain,
% 1.82/2.08      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.08      inference('sup+', [status(thm)], ['248', '249'])).
% 1.82/2.08  thf('251', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.08  thf('252', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.08  thf('253', plain,
% 1.82/2.08      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.08      inference('demod', [status(thm)], ['250', '251', '252'])).
% 1.82/2.08  thf('254', plain,
% 1.82/2.08      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 1.82/2.08      inference('demod', [status(thm)], ['81', '82', '85'])).
% 1.82/2.08  thf('255', plain,
% 1.82/2.08      (![X50 : $i]:
% 1.82/2.08         ((m1_subset_1 @ X50 @ 
% 1.82/2.08           (k1_zfmisc_1 @ 
% 1.82/2.08            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.82/2.08          | ~ (v1_funct_1 @ X50)
% 1.82/2.08          | ~ (v1_relat_1 @ X50))),
% 1.82/2.08      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.82/2.08  thf('256', plain,
% 1.82/2.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.82/2.08         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.82/2.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.82/2.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.82/2.08  thf('257', plain,
% 1.82/2.08      (![X0 : $i]:
% 1.82/2.08         (~ (v1_relat_1 @ X0)
% 1.82/2.08          | ~ (v1_funct_1 @ X0)
% 1.82/2.08          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.82/2.08              = (k2_relat_1 @ X0)))),
% 1.82/2.08      inference('sup-', [status(thm)], ['255', '256'])).
% 1.82/2.08  thf('258', plain,
% 1.82/2.08      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08          (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.08        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.08      inference('sup+', [status(thm)], ['254', '257'])).
% 1.82/2.08  thf('259', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('simplify', [status(thm)], ['52'])).
% 1.82/2.08  thf('260', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.82/2.08      inference('demod', [status(thm)], ['42', '43'])).
% 1.82/2.08  thf('261', plain,
% 1.82/2.08      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08         = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.08      inference('demod', [status(thm)], ['258', '259', '260'])).
% 1.82/2.08  thf('262', plain,
% 1.82/2.08      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08          (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08          = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.82/2.08        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08            != (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.08      inference('demod', [status(thm)], ['246', '247', '253', '261'])).
% 1.82/2.08  thf('263', plain,
% 1.82/2.08      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ 
% 1.82/2.08            (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08            = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.08      inference('simplify', [status(thm)], ['262'])).
% 1.82/2.08  thf('264', plain,
% 1.82/2.08      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))),
% 1.82/2.08      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 1.82/2.08  thf('265', plain,
% 1.82/2.08      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.82/2.08        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.82/2.08            (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.08      inference('demod', [status(thm)], ['263', '264'])).
% 1.82/2.08  thf('266', plain,
% 1.82/2.08      ((~ (v1_relat_1 @ sk_C_1)
% 1.82/2.08        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.08        | ~ (v2_funct_1 @ sk_C_1)
% 1.82/2.08        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.82/2.08            (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.82/2.08      inference('sup-', [status(thm)], ['238', '265'])).
% 1.82/2.08  thf('267', plain, ((v1_relat_1 @ sk_C_1)),
% 1.82/2.08      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.08  thf('268', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('269', plain, ((v2_funct_1 @ sk_C_1)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('270', plain,
% 1.82/2.08      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.82/2.08         (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.82/2.08      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 1.82/2.08  thf('271', plain,
% 1.82/2.08      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.08          (k2_funct_1 @ (k2_funct_1 @ sk_C_1)) @ sk_C_1)),
% 1.82/2.08      inference('demod', [status(thm)], ['237', '270'])).
% 1.82/2.08  thf('272', plain,
% 1.82/2.08      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.82/2.08           sk_C_1)
% 1.82/2.08        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.82/2.08      inference('sup-', [status(thm)], ['214', '271'])).
% 1.82/2.08  thf('273', plain,
% 1.82/2.08      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.08        (k1_zfmisc_1 @ 
% 1.82/2.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('274', plain,
% 1.82/2.08      ((m1_subset_1 @ sk_C_1 @ 
% 1.82/2.08        (k1_zfmisc_1 @ 
% 1.82/2.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf(reflexivity_r2_funct_2, axiom,
% 1.82/2.08    (![A:$i,B:$i,C:$i,D:$i]:
% 1.82/2.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.82/2.08         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.82/2.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.08       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 1.82/2.08  thf('275', plain,
% 1.82/2.08      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.82/2.08         ((r2_funct_2 @ X40 @ X41 @ X42 @ X42)
% 1.82/2.08          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.82/2.08          | ~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.82/2.08          | ~ (v1_funct_1 @ X42)
% 1.82/2.08          | ~ (v1_funct_1 @ X43)
% 1.82/2.08          | ~ (v1_funct_2 @ X43 @ X40 @ X41)
% 1.82/2.08          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 1.82/2.08      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 1.82/2.08  thf('276', plain,
% 1.82/2.08      (![X0 : $i]:
% 1.82/2.08         (~ (m1_subset_1 @ X0 @ 
% 1.82/2.08             (k1_zfmisc_1 @ 
% 1.82/2.08              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.82/2.08          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.82/2.08          | ~ (v1_funct_1 @ X0)
% 1.82/2.08          | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.08          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 1.82/2.08               (u1_struct_0 @ sk_B))
% 1.82/2.08          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.08             sk_C_1 @ sk_C_1))),
% 1.82/2.08      inference('sup-', [status(thm)], ['274', '275'])).
% 1.82/2.08  thf('277', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('278', plain,
% 1.82/2.08      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('279', plain,
% 1.82/2.08      (![X0 : $i]:
% 1.82/2.08         (~ (m1_subset_1 @ X0 @ 
% 1.82/2.08             (k1_zfmisc_1 @ 
% 1.82/2.08              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.82/2.08          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.82/2.08          | ~ (v1_funct_1 @ X0)
% 1.82/2.08          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.82/2.08             sk_C_1 @ sk_C_1))),
% 1.82/2.08      inference('demod', [status(thm)], ['276', '277', '278'])).
% 1.82/2.08  thf('280', plain,
% 1.82/2.08      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.82/2.08         sk_C_1)
% 1.82/2.08        | ~ (v1_funct_1 @ sk_C_1)
% 1.82/2.08        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.82/2.08      inference('sup-', [status(thm)], ['273', '279'])).
% 1.82/2.08  thf('281', plain, ((v1_funct_1 @ sk_C_1)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('282', plain,
% 1.82/2.08      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('283', plain,
% 1.82/2.08      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 1.82/2.08        sk_C_1)),
% 1.82/2.08      inference('demod', [status(thm)], ['280', '281', '282'])).
% 1.82/2.08  thf('284', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 1.82/2.08      inference('demod', [status(thm)], ['272', '283'])).
% 1.82/2.08  thf('285', plain,
% 1.82/2.08      ((((k2_struct_0 @ sk_B) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.08      inference('sup+', [status(thm)], ['1', '284'])).
% 1.82/2.08  thf('286', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('287', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 1.82/2.08      inference('demod', [status(thm)], ['285', '286'])).
% 1.82/2.08  thf('288', plain,
% 1.82/2.08      (![X52 : $i]:
% 1.82/2.08         (~ (v1_xboole_0 @ (k2_struct_0 @ X52))
% 1.82/2.08          | ~ (l1_struct_0 @ X52)
% 1.82/2.08          | (v2_struct_0 @ X52))),
% 1.82/2.08      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.82/2.08  thf('289', plain,
% 1.82/2.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.82/2.08        | (v2_struct_0 @ sk_B)
% 1.82/2.08        | ~ (l1_struct_0 @ sk_B))),
% 1.82/2.08      inference('sup-', [status(thm)], ['287', '288'])).
% 1.82/2.08  thf(rc1_relset_1, axiom,
% 1.82/2.08    (![A:$i,B:$i]:
% 1.82/2.08     ( ?[C:$i]:
% 1.82/2.08       ( ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 1.82/2.08         ( v1_relat_1 @ C ) & ( v1_xboole_0 @ C ) & 
% 1.82/2.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.82/2.08  thf('290', plain,
% 1.82/2.08      (![X37 : $i, X38 : $i]: (v1_xboole_0 @ (sk_C @ X37 @ X38))),
% 1.82/2.08      inference('cnf', [status(esa)], [rc1_relset_1])).
% 1.82/2.08  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.82/2.08  thf('291', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.82/2.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.82/2.08  thf(t3_subset, axiom,
% 1.82/2.08    (![A:$i,B:$i]:
% 1.82/2.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.82/2.08  thf('292', plain,
% 1.82/2.08      (![X4 : $i, X6 : $i]:
% 1.82/2.08         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 1.82/2.08      inference('cnf', [status(esa)], [t3_subset])).
% 1.82/2.08  thf('293', plain,
% 1.82/2.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.82/2.08      inference('sup-', [status(thm)], ['291', '292'])).
% 1.82/2.08  thf(cc3_relset_1, axiom,
% 1.82/2.08    (![A:$i,B:$i]:
% 1.82/2.08     ( ( v1_xboole_0 @ A ) =>
% 1.82/2.08       ( ![C:$i]:
% 1.82/2.08         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.08           ( v1_xboole_0 @ C ) ) ) ))).
% 1.82/2.08  thf('294', plain,
% 1.82/2.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.82/2.08         (~ (v1_xboole_0 @ X26)
% 1.82/2.08          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 1.82/2.08          | (v1_xboole_0 @ X27))),
% 1.82/2.08      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.82/2.08  thf('295', plain,
% 1.82/2.08      (![X1 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X1))),
% 1.82/2.08      inference('sup-', [status(thm)], ['293', '294'])).
% 1.82/2.08  thf('296', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.82/2.08      inference('sup-', [status(thm)], ['290', '295'])).
% 1.82/2.08  thf('297', plain, ((l1_struct_0 @ sk_B)),
% 1.82/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.08  thf('298', plain, ((v2_struct_0 @ sk_B)),
% 1.82/2.08      inference('demod', [status(thm)], ['289', '296', '297'])).
% 1.82/2.08  thf('299', plain, ($false), inference('demod', [status(thm)], ['0', '298'])).
% 1.82/2.08  
% 1.82/2.08  % SZS output end Refutation
% 1.82/2.08  
% 1.82/2.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
