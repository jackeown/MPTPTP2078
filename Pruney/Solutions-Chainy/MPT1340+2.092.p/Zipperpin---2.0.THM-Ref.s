%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lE4uiqQvXs

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:23 EST 2020

% Result     : Theorem 3.74s
% Output     : Refutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  413 (5643 expanded)
%              Number of leaves         :   48 (1655 expanded)
%              Depth                    :   37
%              Number of atoms          : 4286 (125961 expanded)
%              Number of equality atoms :  230 (4114 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('20',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('28',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('37',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('63',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('70',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','71'])).

thf('73',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

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

thf('87',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','94','95','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','80','81','106'])).

thf('108',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('111',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

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

thf('113',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('124',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('133',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X31 ) @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','131','140'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('142',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('143',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('144',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('145',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('146',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('148',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('149',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('151',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relset_1 @ X16 @ X17 @ X18 @ X16 )
        = ( k2_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('152',plain,
    ( ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('154',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k9_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','155'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('157',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k10_relat_1 @ X5 @ X6 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X5 ) @ X6 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('158',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('161',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('162',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relset_1 @ X16 @ X17 @ X18 @ X16 )
        = ( k2_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('173',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('175',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k9_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('178',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['158','177'])).

thf('179',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('180',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','181'])).

thf('183',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('187',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','188','189','190'])).

thf('192',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','191'])).

thf('193',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('194',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('195',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('197',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('198',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('200',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['198','201'])).

thf('203',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['195','202'])).

thf('204',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('205',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('206',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('208',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('209',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('210',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('211',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k10_relat_1 @ X5 @ X6 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X5 ) @ X6 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['209','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['208','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['207','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('220',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('221',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['219','221'])).

thf('223',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('224',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('225',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['222','225'])).

thf('227',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('228',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('229',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('230',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X31 ) @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('231',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('234',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('235',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['231','232','233','234','235'])).

thf('237',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['228','236'])).

thf('238',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('242',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('244',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('245',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('247',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['245','248'])).

thf('250',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['242','249'])).

thf('251',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['227','250'])).

thf('252',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['226','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['218','254'])).

thf('256',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('257',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relset_1 @ X16 @ X17 @ X18 @ X16 )
        = ( k2_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('258',plain,
    ( ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('260',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k9_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('263',plain,
    ( ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['258','261','262'])).

thf('264',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('265',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['255','263','264','265','266'])).

thf('268',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('273',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('274',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(clc,[status(thm)],['271','274'])).

thf('276',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('278',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','277'])).

thf('279',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','278'])).

thf('280',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['192','279'])).

thf('281',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','280'])).

thf('282',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['143','282'])).

thf('284',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('285',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['283','284','285','286'])).

thf('288',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('289',plain,(
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

thf('290',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_funct_2 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('291',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('296',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('297',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['294','295','296','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_C = X0 )
      | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['288','298'])).

thf('300',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_C = X0 )
      | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['299','300'])).

thf('302',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['287','301'])).

thf('303',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('304',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('305',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X31 ) @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('306',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('308',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['239'])).

thf('309',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('310',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('311',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('312',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','188','189','190'])).

thf('314',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['312','313'])).

thf('315',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','278'])).

thf('316',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['314','315'])).

thf('317',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['309','316'])).

thf('318',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['303','318'])).

thf('320',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('321',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['319','320','321','322'])).

thf('324',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('325',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('326',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('327',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('329',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('330',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','191'])).

thf('332',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','278'])).

thf('334',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['332','333'])).

thf('335',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['324','335'])).

thf('337',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('338',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['336','337','338','339'])).

thf('341',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['302','323','340'])).

thf('342',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['142','341'])).

thf('343',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('344',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_funct_2 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('345',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_funct_2 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['343','345'])).

thf('347',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('348',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['346','347','348'])).

thf('350',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('351',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['342','349','350','351','352'])).

thf('354',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['192','279'])).

thf('355',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','353','354'])).

thf('356',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['111','356'])).

thf('358',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['186','187'])).

thf('359',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['357','358','359','360'])).

thf('362',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['346','347','348'])).

thf('363',plain,(
    $false ),
    inference(demod,[status(thm)],['110','361','362'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lE4uiqQvXs
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.74/3.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.74/3.94  % Solved by: fo/fo7.sh
% 3.74/3.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.74/3.94  % done 1183 iterations in 3.490s
% 3.74/3.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.74/3.94  % SZS output start Refutation
% 3.74/3.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.74/3.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.74/3.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.74/3.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.74/3.94  thf(sk_C_type, type, sk_C: $i).
% 3.74/3.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.74/3.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.74/3.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.74/3.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.74/3.94  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.74/3.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.74/3.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.74/3.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.74/3.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.74/3.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.74/3.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.74/3.94  thf(sk_A_type, type, sk_A: $i).
% 3.74/3.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.74/3.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.74/3.94  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.74/3.94  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.74/3.94  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.74/3.94  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 3.74/3.94  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.74/3.94  thf(sk_B_type, type, sk_B: $i).
% 3.74/3.94  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.74/3.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.74/3.94  thf(d3_struct_0, axiom,
% 3.74/3.94    (![A:$i]:
% 3.74/3.94     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.74/3.94  thf('0', plain,
% 3.74/3.94      (![X34 : $i]:
% 3.74/3.94         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.94  thf('1', plain,
% 3.74/3.94      (![X34 : $i]:
% 3.74/3.94         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.94  thf('2', plain,
% 3.74/3.94      (![X34 : $i]:
% 3.74/3.94         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.94  thf(t64_tops_2, conjecture,
% 3.74/3.94    (![A:$i]:
% 3.74/3.94     ( ( l1_struct_0 @ A ) =>
% 3.74/3.94       ( ![B:$i]:
% 3.74/3.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.74/3.94           ( ![C:$i]:
% 3.74/3.94             ( ( ( v1_funct_1 @ C ) & 
% 3.74/3.94                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.74/3.94                 ( m1_subset_1 @
% 3.74/3.94                   C @ 
% 3.74/3.94                   ( k1_zfmisc_1 @
% 3.74/3.94                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.74/3.94               ( ( ( ( k2_relset_1 @
% 3.74/3.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.74/3.94                     ( k2_struct_0 @ B ) ) & 
% 3.74/3.94                   ( v2_funct_1 @ C ) ) =>
% 3.74/3.94                 ( r2_funct_2 @
% 3.74/3.94                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.74/3.94                   ( k2_tops_2 @
% 3.74/3.94                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.74/3.94                     ( k2_tops_2 @
% 3.74/3.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.74/3.94                   C ) ) ) ) ) ) ))).
% 3.74/3.94  thf(zf_stmt_0, negated_conjecture,
% 3.74/3.94    (~( ![A:$i]:
% 3.74/3.94        ( ( l1_struct_0 @ A ) =>
% 3.74/3.94          ( ![B:$i]:
% 3.74/3.94            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.74/3.94              ( ![C:$i]:
% 3.74/3.94                ( ( ( v1_funct_1 @ C ) & 
% 3.74/3.94                    ( v1_funct_2 @
% 3.74/3.94                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.74/3.94                    ( m1_subset_1 @
% 3.74/3.94                      C @ 
% 3.74/3.94                      ( k1_zfmisc_1 @
% 3.74/3.94                        ( k2_zfmisc_1 @
% 3.74/3.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.74/3.94                  ( ( ( ( k2_relset_1 @
% 3.74/3.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.74/3.94                        ( k2_struct_0 @ B ) ) & 
% 3.74/3.94                      ( v2_funct_1 @ C ) ) =>
% 3.74/3.94                    ( r2_funct_2 @
% 3.74/3.94                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.74/3.94                      ( k2_tops_2 @
% 3.74/3.94                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.74/3.94                        ( k2_tops_2 @
% 3.74/3.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.74/3.94                      C ) ) ) ) ) ) ) )),
% 3.74/3.94    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 3.74/3.94  thf('3', plain,
% 3.74/3.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/3.94          sk_C)),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf('4', plain,
% 3.74/3.94      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/3.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/3.94           sk_C)
% 3.74/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.94      inference('sup-', [status(thm)], ['2', '3'])).
% 3.74/3.94  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf('6', plain,
% 3.74/3.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/3.94          sk_C)),
% 3.74/3.94      inference('demod', [status(thm)], ['4', '5'])).
% 3.74/3.94  thf('7', plain,
% 3.74/3.94      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/3.94           sk_C)
% 3.74/3.94        | ~ (l1_struct_0 @ sk_A))),
% 3.74/3.94      inference('sup-', [status(thm)], ['1', '6'])).
% 3.74/3.94  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf('9', plain,
% 3.74/3.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/3.94          sk_C)),
% 3.74/3.94      inference('demod', [status(thm)], ['7', '8'])).
% 3.74/3.94  thf(d1_funct_2, axiom,
% 3.74/3.94    (![A:$i,B:$i,C:$i]:
% 3.74/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.74/3.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.74/3.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.74/3.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.74/3.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.74/3.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.74/3.94  thf(zf_stmt_1, axiom,
% 3.74/3.94    (![B:$i,A:$i]:
% 3.74/3.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.74/3.94       ( zip_tseitin_0 @ B @ A ) ))).
% 3.74/3.94  thf('10', plain,
% 3.74/3.94      (![X19 : $i, X20 : $i]:
% 3.74/3.94         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/3.94  thf('11', plain,
% 3.74/3.94      ((m1_subset_1 @ sk_C @ 
% 3.74/3.94        (k1_zfmisc_1 @ 
% 3.74/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.74/3.94  thf(zf_stmt_3, axiom,
% 3.74/3.94    (![C:$i,B:$i,A:$i]:
% 3.74/3.94     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.74/3.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.74/3.94  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.74/3.94  thf(zf_stmt_5, axiom,
% 3.74/3.94    (![A:$i,B:$i,C:$i]:
% 3.74/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.94       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.74/3.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.74/3.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.74/3.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.74/3.94  thf('12', plain,
% 3.74/3.94      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.74/3.94         (~ (zip_tseitin_0 @ X24 @ X25)
% 3.74/3.94          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 3.74/3.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/3.94  thf('13', plain,
% 3.74/3.94      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/3.94        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.74/3.94      inference('sup-', [status(thm)], ['11', '12'])).
% 3.74/3.94  thf('14', plain,
% 3.74/3.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/3.94        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.74/3.94      inference('sup-', [status(thm)], ['10', '13'])).
% 3.74/3.94  thf('15', plain,
% 3.74/3.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf('16', plain,
% 3.74/3.94      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.74/3.94         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 3.74/3.94          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 3.74/3.94          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/3.94  thf('17', plain,
% 3.74/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/3.94        | ((u1_struct_0 @ sk_A)
% 3.74/3.94            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.74/3.94      inference('sup-', [status(thm)], ['15', '16'])).
% 3.74/3.94  thf('18', plain,
% 3.74/3.94      ((m1_subset_1 @ sk_C @ 
% 3.74/3.94        (k1_zfmisc_1 @ 
% 3.74/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf(t38_relset_1, axiom,
% 3.74/3.94    (![A:$i,B:$i,C:$i]:
% 3.74/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.94       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 3.74/3.94         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.74/3.94  thf('19', plain,
% 3.74/3.94      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.94         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 3.74/3.94            = (k1_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.94          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.94  thf('20', plain,
% 3.74/3.94      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.94         (u1_struct_0 @ sk_B))
% 3.74/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.94      inference('sup-', [status(thm)], ['18', '19'])).
% 3.74/3.94  thf('21', plain,
% 3.74/3.94      ((m1_subset_1 @ sk_C @ 
% 3.74/3.94        (k1_zfmisc_1 @ 
% 3.74/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf(redefinition_k8_relset_1, axiom,
% 3.74/3.94    (![A:$i,B:$i,C:$i,D:$i]:
% 3.74/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.94       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 3.74/3.94  thf('22', plain,
% 3.74/3.94      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.74/3.94         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.74/3.94          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 3.74/3.94      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/3.94  thf('23', plain,
% 3.74/3.94      (![X0 : $i]:
% 3.74/3.94         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.94           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/3.94      inference('sup-', [status(thm)], ['21', '22'])).
% 3.74/3.94  thf('24', plain,
% 3.74/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.94      inference('demod', [status(thm)], ['20', '23'])).
% 3.74/3.94  thf('25', plain,
% 3.74/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/3.94        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))))),
% 3.74/3.94      inference('demod', [status(thm)], ['17', '24'])).
% 3.74/3.94  thf('26', plain,
% 3.74/3.94      (![X34 : $i]:
% 3.74/3.94         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.94  thf('27', plain,
% 3.74/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.94      inference('demod', [status(thm)], ['20', '23'])).
% 3.74/3.94  thf('28', plain,
% 3.74/3.94      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/3.94          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.74/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.94      inference('sup+', [status(thm)], ['26', '27'])).
% 3.74/3.94  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.94  thf('30', plain,
% 3.74/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('demod', [status(thm)], ['28', '29'])).
% 3.74/3.95  thf('31', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('32', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('33', plain,
% 3.74/3.95      (((m1_subset_1 @ sk_C @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup+', [status(thm)], ['31', '32'])).
% 3.74/3.95  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('35', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['33', '34'])).
% 3.74/3.95  thf('36', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 3.74/3.95            = (k1_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('37', plain,
% 3.74/3.95      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95         (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['35', '36'])).
% 3.74/3.95  thf('38', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['33', '34'])).
% 3.74/3.95  thf('39', plain,
% 3.74/3.95      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.74/3.95          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/3.95  thf('40', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['38', '39'])).
% 3.74/3.95  thf('41', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('demod', [status(thm)], ['37', '40'])).
% 3.74/3.95  thf('42', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup+', [status(thm)], ['30', '41'])).
% 3.74/3.95  thf('43', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/3.95        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['25', '42'])).
% 3.74/3.95  thf('44', plain,
% 3.74/3.95      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/3.95        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['14', '43'])).
% 3.74/3.95  thf('45', plain,
% 3.74/3.95      (![X19 : $i, X20 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/3.95  thf('46', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('47', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('48', plain,
% 3.74/3.95      (((m1_subset_1 @ sk_C @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_A))),
% 3.74/3.95      inference('sup+', [status(thm)], ['46', '47'])).
% 3.74/3.95  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('50', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('51', plain,
% 3.74/3.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.74/3.95         (~ (zip_tseitin_0 @ X24 @ X25)
% 3.74/3.95          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 3.74/3.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/3.95  thf('52', plain,
% 3.74/3.95      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['50', '51'])).
% 3.74/3.95  thf('53', plain,
% 3.74/3.95      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/3.95        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['45', '52'])).
% 3.74/3.95  thf('54', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('55', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('56', plain,
% 3.74/3.95      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_A))),
% 3.74/3.95      inference('sup+', [status(thm)], ['54', '55'])).
% 3.74/3.95  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('58', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['56', '57'])).
% 3.74/3.95  thf('59', plain,
% 3.74/3.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.74/3.95         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 3.74/3.95          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 3.74/3.95          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/3.95  thf('60', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_A)
% 3.74/3.95            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['58', '59'])).
% 3.74/3.95  thf('61', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('62', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 3.74/3.95            = (k1_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('63', plain,
% 3.74/3.95      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95         (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['61', '62'])).
% 3.74/3.95  thf('64', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('65', plain,
% 3.74/3.95      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.74/3.95          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/3.95  thf('66', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['64', '65'])).
% 3.74/3.95  thf('67', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('demod', [status(thm)], ['63', '66'])).
% 3.74/3.95  thf('68', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['60', '67'])).
% 3.74/3.95  thf('69', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup+', [status(thm)], ['30', '41'])).
% 3.74/3.95  thf('70', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['68', '69'])).
% 3.74/3.95  thf('71', plain,
% 3.74/3.95      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['53', '70'])).
% 3.74/3.95  thf('72', plain,
% 3.74/3.95      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 3.74/3.95        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/3.95        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 3.74/3.95      inference('sup+', [status(thm)], ['44', '71'])).
% 3.74/3.95  thf('73', plain,
% 3.74/3.95      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 3.74/3.95      inference('simplify', [status(thm)], ['72'])).
% 3.74/3.95  thf(fc2_struct_0, axiom,
% 3.74/3.95    (![A:$i]:
% 3.74/3.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.74/3.95       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.74/3.95  thf('74', plain,
% 3.74/3.95      (![X35 : $i]:
% 3.74/3.95         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 3.74/3.95          | ~ (l1_struct_0 @ X35)
% 3.74/3.95          | (v2_struct_0 @ X35))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.74/3.95  thf('75', plain,
% 3.74/3.95      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.74/3.95        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 3.74/3.95        | (v2_struct_0 @ sk_B)
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup-', [status(thm)], ['73', '74'])).
% 3.74/3.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.74/3.95  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/3.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/3.95  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('78', plain,
% 3.74/3.95      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.74/3.95  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('80', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/3.95      inference('clc', [status(thm)], ['78', '79'])).
% 3.74/3.95  thf('81', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/3.95      inference('clc', [status(thm)], ['78', '79'])).
% 3.74/3.95  thf('82', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('83', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('84', plain,
% 3.74/3.95      (((m1_subset_1 @ sk_C @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup+', [status(thm)], ['82', '83'])).
% 3.74/3.95  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('86', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf(d4_tops_2, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i]:
% 3.74/3.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.74/3.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/3.95       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.74/3.95         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.74/3.95  thf('87', plain,
% 3.74/3.95      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.74/3.95         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 3.74/3.95          | ~ (v2_funct_1 @ X38)
% 3.74/3.95          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 3.74/3.95          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.74/3.95          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.74/3.95          | ~ (v1_funct_1 @ X38))),
% 3.74/3.95      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.74/3.95  thf('88', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/3.95        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            = (k2_funct_1 @ sk_C))
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            != (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['86', '87'])).
% 3.74/3.95  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('90', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('91', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['56', '57'])).
% 3.74/3.95  thf('92', plain,
% 3.74/3.95      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup+', [status(thm)], ['90', '91'])).
% 3.74/3.95  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('94', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['92', '93'])).
% 3.74/3.95  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('96', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('97', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('98', plain,
% 3.74/3.95      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('99', plain,
% 3.74/3.95      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95          = (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_A))),
% 3.74/3.95      inference('sup+', [status(thm)], ['97', '98'])).
% 3.74/3.95  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('101', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['99', '100'])).
% 3.74/3.95  thf('102', plain,
% 3.74/3.95      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95          = (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup+', [status(thm)], ['96', '101'])).
% 3.74/3.95  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('104', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['102', '103'])).
% 3.74/3.95  thf('105', plain,
% 3.74/3.95      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95          = (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['88', '89', '94', '95', '104'])).
% 3.74/3.95  thf('106', plain,
% 3.74/3.95      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_funct_1 @ sk_C))),
% 3.74/3.95      inference('simplify', [status(thm)], ['105'])).
% 3.74/3.95  thf('107', plain,
% 3.74/3.95      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95          sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['9', '80', '81', '106'])).
% 3.74/3.95  thf('108', plain,
% 3.74/3.95      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           sk_C)
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup-', [status(thm)], ['0', '107'])).
% 3.74/3.95  thf('109', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('110', plain,
% 3.74/3.95      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95          sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['108', '109'])).
% 3.74/3.95  thf(fc6_funct_1, axiom,
% 3.74/3.95    (![A:$i]:
% 3.74/3.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.74/3.95       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.74/3.95         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.74/3.95         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.74/3.95  thf('111', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('112', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf(t31_funct_2, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i]:
% 3.74/3.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.74/3.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/3.95       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.74/3.95         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.74/3.95           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.74/3.95           ( m1_subset_1 @
% 3.74/3.95             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.74/3.95  thf('113', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (m1_subset_1 @ (k2_funct_1 @ X31) @ 
% 3.74/3.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('114', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            != (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['112', '113'])).
% 3.74/3.95  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('116', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['92', '93'])).
% 3.74/3.95  thf('117', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['102', '103'])).
% 3.74/3.95  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('119', plain,
% 3.74/3.95      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/3.95        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 3.74/3.95  thf('120', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['119'])).
% 3.74/3.95  thf('121', plain,
% 3.74/3.95      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.74/3.95         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 3.74/3.95          | ~ (v2_funct_1 @ X38)
% 3.74/3.95          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 3.74/3.95          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.74/3.95          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.74/3.95          | ~ (v1_funct_1 @ X38))),
% 3.74/3.95      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.74/3.95  thf('122', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95             (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['120', '121'])).
% 3.74/3.95  thf('123', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf('124', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (v1_funct_1 @ (k2_funct_1 @ X31))
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('125', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/3.95        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            != (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['123', '124'])).
% 3.74/3.95  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('127', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['92', '93'])).
% 3.74/3.95  thf('128', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['102', '103'])).
% 3.74/3.95  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('130', plain,
% 3.74/3.95      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 3.74/3.95  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/3.95      inference('simplify', [status(thm)], ['130'])).
% 3.74/3.95  thf('132', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf('133', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (v1_funct_2 @ (k2_funct_1 @ X31) @ X32 @ X33)
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('134', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            != (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['132', '133'])).
% 3.74/3.95  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('136', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['92', '93'])).
% 3.74/3.95  thf('137', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['102', '103'])).
% 3.74/3.95  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('139', plain,
% 3.74/3.95      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95         (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 3.74/3.95  thf('140', plain,
% 3.74/3.95      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95        (k2_struct_0 @ sk_A))),
% 3.74/3.95      inference('simplify', [status(thm)], ['139'])).
% 3.74/3.95  thf('141', plain,
% 3.74/3.95      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('demod', [status(thm)], ['122', '131', '140'])).
% 3.74/3.95  thf(t65_funct_1, axiom,
% 3.74/3.95    (![A:$i]:
% 3.74/3.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.74/3.95       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.74/3.95  thf('142', plain,
% 3.74/3.95      (![X7 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X7)
% 3.74/3.95          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 3.74/3.95          | ~ (v1_funct_1 @ X7)
% 3.74/3.95          | ~ (v1_relat_1 @ X7))),
% 3.74/3.95      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/3.95  thf('143', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('144', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['119'])).
% 3.74/3.95  thf('145', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (m1_subset_1 @ (k2_funct_1 @ X31) @ 
% 3.74/3.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('146', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95             (k2_struct_0 @ sk_A))
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['144', '145'])).
% 3.74/3.95  thf('147', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/3.95      inference('simplify', [status(thm)], ['130'])).
% 3.74/3.95  thf('148', plain,
% 3.74/3.95      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95        (k2_struct_0 @ sk_A))),
% 3.74/3.95      inference('simplify', [status(thm)], ['139'])).
% 3.74/3.95  thf('149', plain,
% 3.74/3.95      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['146', '147', '148'])).
% 3.74/3.95  thf('150', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['119'])).
% 3.74/3.95  thf('151', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k7_relset_1 @ X16 @ X17 @ X18 @ X16)
% 3.74/3.95            = (k2_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('152', plain,
% 3.74/3.95      (((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95         (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['150', '151'])).
% 3.74/3.95  thf('153', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['119'])).
% 3.74/3.95  thf(redefinition_k7_relset_1, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i,D:$i]:
% 3.74/3.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.95       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 3.74/3.95  thf('154', plain,
% 3.74/3.95      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 3.74/3.95          | ((k7_relset_1 @ X9 @ X10 @ X8 @ X11) = (k9_relat_1 @ X8 @ X11)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.74/3.95  thf('155', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_funct_1 @ sk_C) @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['153', '154'])).
% 3.74/3.95  thf('156', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['152', '155'])).
% 3.74/3.95  thf(t155_funct_1, axiom,
% 3.74/3.95    (![A:$i,B:$i]:
% 3.74/3.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.74/3.95       ( ( v2_funct_1 @ B ) =>
% 3.74/3.95         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 3.74/3.95  thf('157', plain,
% 3.74/3.95      (![X5 : $i, X6 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X5)
% 3.74/3.95          | ((k10_relat_1 @ X5 @ X6) = (k9_relat_1 @ (k2_funct_1 @ X5) @ X6))
% 3.74/3.95          | ~ (v1_funct_1 @ X5)
% 3.74/3.95          | ~ (v1_relat_1 @ X5))),
% 3.74/3.95      inference('cnf', [status(esa)], [t155_funct_1])).
% 3.74/3.95  thf('158', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('159', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('160', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('161', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (m1_subset_1 @ (k2_funct_1 @ X31) @ 
% 3.74/3.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('162', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            != (u1_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['160', '161'])).
% 3.74/3.95  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('164', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['56', '57'])).
% 3.74/3.95  thf('165', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['99', '100'])).
% 3.74/3.95  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('167', plain,
% 3.74/3.95      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/3.95        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 3.74/3.95  thf('168', plain,
% 3.74/3.95      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B)
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['159', '167'])).
% 3.74/3.95  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('170', plain,
% 3.74/3.95      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 3.74/3.95      inference('demod', [status(thm)], ['168', '169'])).
% 3.74/3.95  thf('171', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['170'])).
% 3.74/3.95  thf('172', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k7_relset_1 @ X16 @ X17 @ X18 @ X16)
% 3.74/3.95            = (k2_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('173', plain,
% 3.74/3.95      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95         (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['171', '172'])).
% 3.74/3.95  thf('174', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['170'])).
% 3.74/3.95  thf('175', plain,
% 3.74/3.95      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 3.74/3.95          | ((k7_relset_1 @ X9 @ X10 @ X8 @ X11) = (k9_relat_1 @ X8 @ X11)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.74/3.95  thf('176', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_funct_1 @ sk_C) @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['174', '175'])).
% 3.74/3.95  thf('177', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['173', '176'])).
% 3.74/3.95  thf('178', plain,
% 3.74/3.95      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.74/3.95          = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95             (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup+', [status(thm)], ['158', '177'])).
% 3.74/3.95  thf('179', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['152', '155'])).
% 3.74/3.95  thf('180', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('181', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['178', '179', '180'])).
% 3.74/3.95  thf('182', plain,
% 3.74/3.95      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/3.95          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))
% 3.74/3.95        | ~ (v1_relat_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C))),
% 3.74/3.95      inference('sup+', [status(thm)], ['157', '181'])).
% 3.74/3.95  thf('183', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup+', [status(thm)], ['30', '41'])).
% 3.74/3.95  thf('184', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(cc2_relat_1, axiom,
% 3.74/3.95    (![A:$i]:
% 3.74/3.95     ( ( v1_relat_1 @ A ) =>
% 3.74/3.95       ( ![B:$i]:
% 3.74/3.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.74/3.95  thf('185', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.74/3.95          | (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X1))),
% 3.74/3.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.74/3.95  thf('186', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ 
% 3.74/3.95           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 3.74/3.95        | (v1_relat_1 @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['184', '185'])).
% 3.74/3.95  thf(fc6_relat_1, axiom,
% 3.74/3.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.74/3.95  thf('187', plain,
% 3.74/3.95      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.74/3.95  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('191', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['182', '183', '188', '189', '190'])).
% 3.74/3.95  thf('192', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['156', '191'])).
% 3.74/3.95  thf('193', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['92', '93'])).
% 3.74/3.95  thf('194', plain,
% 3.74/3.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.74/3.95         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 3.74/3.95          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 3.74/3.95          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/3.95  thf('195', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_A)
% 3.74/3.95            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['193', '194'])).
% 3.74/3.95  thf('196', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf('197', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 3.74/3.95            = (k1_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('198', plain,
% 3.74/3.95      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95         (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['196', '197'])).
% 3.74/3.95  thf('199', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf('200', plain,
% 3.74/3.95      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.74/3.95          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/3.95  thf('201', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['199', '200'])).
% 3.74/3.95  thf('202', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('demod', [status(thm)], ['198', '201'])).
% 3.74/3.95  thf('203', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['195', '202'])).
% 3.74/3.95  thf('204', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['84', '85'])).
% 3.74/3.95  thf('205', plain,
% 3.74/3.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.74/3.95         (~ (zip_tseitin_0 @ X24 @ X25)
% 3.74/3.95          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 3.74/3.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/3.95  thf('206', plain,
% 3.74/3.95      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['204', '205'])).
% 3.74/3.95  thf('207', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('208', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('209', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('210', plain,
% 3.74/3.95      (![X7 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X7)
% 3.74/3.95          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 3.74/3.95          | ~ (v1_funct_1 @ X7)
% 3.74/3.95          | ~ (v1_relat_1 @ X7))),
% 3.74/3.95      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/3.95  thf('211', plain,
% 3.74/3.95      (![X5 : $i, X6 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X5)
% 3.74/3.95          | ((k10_relat_1 @ X5 @ X6) = (k9_relat_1 @ (k2_funct_1 @ X5) @ X6))
% 3.74/3.95          | ~ (v1_funct_1 @ X5)
% 3.74/3.95          | ~ (v1_relat_1 @ X5))),
% 3.74/3.95      inference('cnf', [status(esa)], [t155_funct_1])).
% 3.74/3.95  thf('212', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.74/3.95          | ~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/3.95      inference('sup+', [status(thm)], ['210', '211'])).
% 3.74/3.95  thf('213', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X0)
% 3.74/3.95          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['209', '212'])).
% 3.74/3.95  thf('214', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.74/3.95          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X0))),
% 3.74/3.95      inference('simplify', [status(thm)], ['213'])).
% 3.74/3.95  thf('215', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['208', '214'])).
% 3.74/3.95  thf('216', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.74/3.95          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X0))),
% 3.74/3.95      inference('simplify', [status(thm)], ['215'])).
% 3.74/3.95  thf('217', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['207', '216'])).
% 3.74/3.95  thf('218', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.74/3.95          | ~ (v2_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_relat_1 @ X0))),
% 3.74/3.95      inference('simplify', [status(thm)], ['217'])).
% 3.74/3.95  thf('219', plain,
% 3.74/3.95      (![X19 : $i, X20 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/3.95  thf('220', plain,
% 3.74/3.95      (![X19 : $i, X20 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/3.95  thf('221', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 3.74/3.95      inference('simplify', [status(thm)], ['220'])).
% 3.74/3.95  thf('222', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.74/3.95      inference('sup+', [status(thm)], ['219', '221'])).
% 3.74/3.95  thf('223', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['119'])).
% 3.74/3.95  thf('224', plain,
% 3.74/3.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.74/3.95         (~ (zip_tseitin_0 @ X24 @ X25)
% 3.74/3.95          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 3.74/3.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/3.95  thf('225', plain,
% 3.74/3.95      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95         (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['223', '224'])).
% 3.74/3.95  thf('226', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.74/3.95          | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95             (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['222', '225'])).
% 3.74/3.95  thf('227', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('228', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('229', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('230', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (v1_funct_2 @ (k2_funct_1 @ X31) @ X32 @ X33)
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('231', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95            != (u1_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['229', '230'])).
% 3.74/3.95  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('233', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['56', '57'])).
% 3.74/3.95  thf('234', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['99', '100'])).
% 3.74/3.95  thf('235', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('236', plain,
% 3.74/3.95      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95         (k2_struct_0 @ sk_A))
% 3.74/3.95        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['231', '232', '233', '234', '235'])).
% 3.74/3.95  thf('237', plain,
% 3.74/3.95      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B)
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['228', '236'])).
% 3.74/3.95  thf('238', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('239', plain,
% 3.74/3.95      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('demod', [status(thm)], ['237', '238'])).
% 3.74/3.95  thf('240', plain,
% 3.74/3.95      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95        (k2_struct_0 @ sk_A))),
% 3.74/3.95      inference('simplify', [status(thm)], ['239'])).
% 3.74/3.95  thf('241', plain,
% 3.74/3.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.74/3.95         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 3.74/3.95          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 3.74/3.95          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/3.95  thf('242', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (u1_struct_0 @ sk_B))
% 3.74/3.95        | ((u1_struct_0 @ sk_B)
% 3.74/3.95            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95               (k2_funct_1 @ sk_C))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['240', '241'])).
% 3.74/3.95  thf('243', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['170'])).
% 3.74/3.95  thf('244', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 3.74/3.95            = (k1_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('245', plain,
% 3.74/3.95      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95         (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 3.74/3.95         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['243', '244'])).
% 3.74/3.95  thf('246', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['170'])).
% 3.74/3.95  thf('247', plain,
% 3.74/3.95      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.74/3.95          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/3.95  thf('248', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['246', '247'])).
% 3.74/3.95  thf('249', plain,
% 3.74/3.95      (((k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 3.74/3.95         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['245', '248'])).
% 3.74/3.95  thf('250', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (u1_struct_0 @ sk_B))
% 3.74/3.95        | ((u1_struct_0 @ sk_B)
% 3.74/3.95            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('demod', [status(thm)], ['242', '249'])).
% 3.74/3.95  thf('251', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_struct_0 @ sk_B))
% 3.74/3.95        | ~ (l1_struct_0 @ sk_B)
% 3.74/3.95        | ((u1_struct_0 @ sk_B)
% 3.74/3.95            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['227', '250'])).
% 3.74/3.95  thf('252', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('253', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95           (k2_struct_0 @ sk_B))
% 3.74/3.95        | ((u1_struct_0 @ sk_B)
% 3.74/3.95            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('demod', [status(thm)], ['251', '252'])).
% 3.74/3.95  thf('254', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.74/3.95          | ((u1_struct_0 @ sk_B)
% 3.74/3.95              = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['226', '253'])).
% 3.74/3.95  thf('255', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (((u1_struct_0 @ sk_B) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 3.74/3.95          | ~ (v1_relat_1 @ sk_C)
% 3.74/3.95          | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95          | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 3.74/3.95      inference('sup+', [status(thm)], ['218', '254'])).
% 3.74/3.95  thf('256', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('257', plain,
% 3.74/3.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (((k7_relset_1 @ X16 @ X17 @ X18 @ X16)
% 3.74/3.95            = (k2_relset_1 @ X16 @ X17 @ X18))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.74/3.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/3.95  thf('258', plain,
% 3.74/3.95      (((k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95         (k2_struct_0 @ sk_A))
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['256', '257'])).
% 3.74/3.95  thf('259', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('260', plain,
% 3.74/3.95      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 3.74/3.95          | ((k7_relset_1 @ X9 @ X10 @ X8 @ X11) = (k9_relat_1 @ X8 @ X11)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.74/3.95  thf('261', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           X0) = (k9_relat_1 @ sk_C @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['259', '260'])).
% 3.74/3.95  thf('262', plain,
% 3.74/3.95      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/3.95         = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['99', '100'])).
% 3.74/3.95  thf('263', plain,
% 3.74/3.95      (((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['258', '261', '262'])).
% 3.74/3.95  thf('264', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('265', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('266', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('267', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))
% 3.74/3.95          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 3.74/3.95      inference('demod', [status(thm)], ['255', '263', '264', '265', '266'])).
% 3.74/3.95  thf('268', plain,
% 3.74/3.95      (![X35 : $i]:
% 3.74/3.95         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 3.74/3.95          | ~ (l1_struct_0 @ X35)
% 3.74/3.95          | (v2_struct_0 @ X35))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.74/3.95  thf('269', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/3.95          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.74/3.95          | (v2_struct_0 @ sk_B)
% 3.74/3.95          | ~ (l1_struct_0 @ sk_B))),
% 3.74/3.95      inference('sup-', [status(thm)], ['267', '268'])).
% 3.74/3.95  thf('270', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('271', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/3.95          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.74/3.95          | (v2_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['269', '270'])).
% 3.74/3.95  thf('272', plain,
% 3.74/3.95      (![X19 : $i, X20 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/3.95  thf('273', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/3.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/3.95  thf('274', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.74/3.95      inference('sup+', [status(thm)], ['272', '273'])).
% 3.74/3.95  thf('275', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         ((v2_struct_0 @ sk_B) | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 3.74/3.95      inference('clc', [status(thm)], ['271', '274'])).
% 3.74/3.95  thf('276', plain, (~ (v2_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('277', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)),
% 3.74/3.95      inference('clc', [status(thm)], ['275', '276'])).
% 3.74/3.95  thf('278', plain,
% 3.74/3.95      ((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 3.74/3.95      inference('demod', [status(thm)], ['206', '277'])).
% 3.74/3.95  thf('279', plain,
% 3.74/3.95      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['203', '278'])).
% 3.74/3.95  thf('280', plain,
% 3.74/3.95      (((k2_struct_0 @ sk_A)
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['192', '279'])).
% 3.74/3.95  thf('281', plain,
% 3.74/3.95      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95         (k1_zfmisc_1 @ 
% 3.74/3.95          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['149', '280'])).
% 3.74/3.95  thf('282', plain,
% 3.74/3.95      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['281'])).
% 3.74/3.95  thf('283', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           (k1_zfmisc_1 @ 
% 3.74/3.95            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['143', '282'])).
% 3.74/3.95  thf('284', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('285', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('286', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('287', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['283', '284', '285', '286'])).
% 3.74/3.95  thf('288', plain,
% 3.74/3.95      (![X34 : $i]:
% 3.74/3.95         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 3.74/3.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/3.95  thf('289', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(redefinition_r2_funct_2, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i,D:$i]:
% 3.74/3.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.74/3.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.74/3.95         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.74/3.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/3.95       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.74/3.95  thf('290', plain,
% 3.74/3.95      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.74/3.95          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 3.74/3.95          | ~ (v1_funct_1 @ X27)
% 3.74/3.95          | ~ (v1_funct_1 @ X30)
% 3.74/3.95          | ~ (v1_funct_2 @ X30 @ X28 @ X29)
% 3.74/3.95          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.74/3.95          | ((X27) = (X30))
% 3.74/3.95          | ~ (r2_funct_2 @ X28 @ X29 @ X27 @ X30))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.74/3.95  thf('291', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95             X0)
% 3.74/3.95          | ((sk_C) = (X0))
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ 
% 3.74/3.95               (k1_zfmisc_1 @ 
% 3.74/3.95                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['289', '290'])).
% 3.74/3.95  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('293', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('294', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95             X0)
% 3.74/3.95          | ((sk_C) = (X0))
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ 
% 3.74/3.95               (k1_zfmisc_1 @ 
% 3.74/3.95                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95          | ~ (v1_funct_1 @ X0))),
% 3.74/3.95      inference('demod', [status(thm)], ['291', '292', '293'])).
% 3.74/3.95  thf('295', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/3.95      inference('clc', [status(thm)], ['78', '79'])).
% 3.74/3.95  thf('296', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/3.95      inference('clc', [status(thm)], ['78', '79'])).
% 3.74/3.95  thf('297', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/3.95      inference('clc', [status(thm)], ['78', '79'])).
% 3.74/3.95  thf('298', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95             X0)
% 3.74/3.95          | ((sk_C) = (X0))
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ 
% 3.74/3.95               (k1_zfmisc_1 @ 
% 3.74/3.95                (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95          | ~ (v1_funct_1 @ X0))),
% 3.74/3.95      inference('demod', [status(thm)], ['294', '295', '296', '297'])).
% 3.74/3.95  thf('299', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X0 @ 
% 3.74/3.95             (k1_zfmisc_1 @ 
% 3.74/3.95              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95          | ~ (l1_struct_0 @ sk_B)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95          | ((sk_C) = (X0))
% 3.74/3.95          | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95               sk_C @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['288', '298'])).
% 3.74/3.95  thf('300', plain, ((l1_struct_0 @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('301', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X0 @ 
% 3.74/3.95             (k1_zfmisc_1 @ 
% 3.74/3.95              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95          | ((sk_C) = (X0))
% 3.74/3.95          | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95               sk_C @ X0))),
% 3.74/3.95      inference('demod', [status(thm)], ['299', '300'])).
% 3.74/3.95  thf('302', plain,
% 3.74/3.95      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95             (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['287', '301'])).
% 3.74/3.95  thf('303', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('304', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['170'])).
% 3.74/3.95  thf('305', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (v1_funct_2 @ (k2_funct_1 @ X31) @ X32 @ X33)
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('306', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95             (k2_struct_0 @ sk_A))
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['304', '305'])).
% 3.74/3.95  thf('307', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/3.95      inference('simplify', [status(thm)], ['130'])).
% 3.74/3.95  thf('308', plain,
% 3.74/3.95      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/3.95        (k2_struct_0 @ sk_A))),
% 3.74/3.95      inference('simplify', [status(thm)], ['239'])).
% 3.74/3.95  thf('309', plain,
% 3.74/3.95      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95         (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['306', '307', '308'])).
% 3.74/3.95  thf('310', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['173', '176'])).
% 3.74/3.95  thf('311', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.74/3.95         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['178', '179', '180'])).
% 3.74/3.95  thf('312', plain,
% 3.74/3.95      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['310', '311'])).
% 3.74/3.95  thf('313', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['182', '183', '188', '189', '190'])).
% 3.74/3.95  thf('314', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['312', '313'])).
% 3.74/3.95  thf('315', plain,
% 3.74/3.95      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['203', '278'])).
% 3.74/3.95  thf('316', plain,
% 3.74/3.95      (((k2_struct_0 @ sk_A)
% 3.74/3.95         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['314', '315'])).
% 3.74/3.95  thf('317', plain,
% 3.74/3.95      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95         (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['309', '316'])).
% 3.74/3.95  thf('318', plain,
% 3.74/3.95      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('simplify', [status(thm)], ['317'])).
% 3.74/3.95  thf('319', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['303', '318'])).
% 3.74/3.95  thf('320', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('321', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('322', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('323', plain,
% 3.74/3.95      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/3.95        (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['319', '320', '321', '322'])).
% 3.74/3.95  thf('324', plain,
% 3.74/3.95      (![X4 : $i]:
% 3.74/3.95         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.74/3.95          | ~ (v2_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_funct_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X4))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/3.95  thf('325', plain,
% 3.74/3.95      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['119'])).
% 3.74/3.95  thf('326', plain,
% 3.74/3.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.74/3.95         (~ (v2_funct_1 @ X31)
% 3.74/3.95          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 3.74/3.95          | (v1_funct_1 @ (k2_funct_1 @ X31))
% 3.74/3.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.74/3.95          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 3.74/3.95          | ~ (v1_funct_1 @ X31))),
% 3.74/3.95      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/3.95  thf('327', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95             (k2_struct_0 @ sk_A))
% 3.74/3.95        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['325', '326'])).
% 3.74/3.95  thf('328', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/3.95      inference('simplify', [status(thm)], ['130'])).
% 3.74/3.95  thf('329', plain,
% 3.74/3.95      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/3.95        (k2_struct_0 @ sk_A))),
% 3.74/3.95      inference('simplify', [status(thm)], ['139'])).
% 3.74/3.95  thf('330', plain,
% 3.74/3.95      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['327', '328', '329'])).
% 3.74/3.95  thf('331', plain,
% 3.74/3.95      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['156', '191'])).
% 3.74/3.95  thf('332', plain,
% 3.74/3.95      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['330', '331'])).
% 3.74/3.95  thf('333', plain,
% 3.74/3.95      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 3.74/3.95      inference('demod', [status(thm)], ['203', '278'])).
% 3.74/3.95  thf('334', plain,
% 3.74/3.95      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['332', '333'])).
% 3.74/3.95  thf('335', plain,
% 3.74/3.95      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['334'])).
% 3.74/3.95  thf('336', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['324', '335'])).
% 3.74/3.95  thf('337', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('338', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('339', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('340', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['336', '337', '338', '339'])).
% 3.74/3.95  thf('341', plain,
% 3.74/3.95      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/3.95        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/3.95      inference('demod', [status(thm)], ['302', '323', '340'])).
% 3.74/3.95  thf('342', plain,
% 3.74/3.95      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           sk_C)
% 3.74/3.95        | ~ (v1_relat_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['142', '341'])).
% 3.74/3.95  thf('343', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_C @ 
% 3.74/3.95        (k1_zfmisc_1 @ 
% 3.74/3.95         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '49'])).
% 3.74/3.95  thf('344', plain,
% 3.74/3.95      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.74/3.95          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 3.74/3.95          | ~ (v1_funct_1 @ X27)
% 3.74/3.95          | ~ (v1_funct_1 @ X30)
% 3.74/3.95          | ~ (v1_funct_2 @ X30 @ X28 @ X29)
% 3.74/3.95          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.74/3.95          | (r2_funct_2 @ X28 @ X29 @ X27 @ X30)
% 3.74/3.95          | ((X27) != (X30)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.74/3.95  thf('345', plain,
% 3.74/3.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.74/3.95         ((r2_funct_2 @ X28 @ X29 @ X30 @ X30)
% 3.74/3.95          | ~ (v1_funct_1 @ X30)
% 3.74/3.95          | ~ (v1_funct_2 @ X30 @ X28 @ X29)
% 3.74/3.95          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.74/3.95      inference('simplify', [status(thm)], ['344'])).
% 3.74/3.95  thf('346', plain,
% 3.74/3.95      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/3.95           sk_C))),
% 3.74/3.95      inference('sup-', [status(thm)], ['343', '345'])).
% 3.74/3.95  thf('347', plain,
% 3.74/3.95      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/3.95      inference('demod', [status(thm)], ['56', '57'])).
% 3.74/3.95  thf('348', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('349', plain,
% 3.74/3.95      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['346', '347', '348'])).
% 3.74/3.95  thf('350', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('351', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('352', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('353', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['342', '349', '350', '351', '352'])).
% 3.74/3.95  thf('354', plain,
% 3.74/3.95      (((k2_struct_0 @ sk_A)
% 3.74/3.95         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)))),
% 3.74/3.95      inference('demod', [status(thm)], ['192', '279'])).
% 3.74/3.95  thf('355', plain,
% 3.74/3.95      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95          (k2_funct_1 @ sk_C)) = (sk_C))
% 3.74/3.95        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 3.74/3.95      inference('demod', [status(thm)], ['141', '353', '354'])).
% 3.74/3.95  thf('356', plain,
% 3.74/3.95      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/3.95        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 3.74/3.95      inference('simplify', [status(thm)], ['355'])).
% 3.74/3.95  thf('357', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_C)
% 3.74/3.95        | ~ (v2_funct_1 @ sk_C)
% 3.74/3.95        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['111', '356'])).
% 3.74/3.95  thf('358', plain, ((v1_relat_1 @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['186', '187'])).
% 3.74/3.95  thf('359', plain, ((v1_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('360', plain, ((v2_funct_1 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('361', plain,
% 3.74/3.95      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/3.95         (k2_funct_1 @ sk_C)) = (sk_C))),
% 3.74/3.95      inference('demod', [status(thm)], ['357', '358', '359', '360'])).
% 3.74/3.95  thf('362', plain,
% 3.74/3.95      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 3.74/3.95      inference('demod', [status(thm)], ['346', '347', '348'])).
% 3.74/3.95  thf('363', plain, ($false),
% 3.74/3.95      inference('demod', [status(thm)], ['110', '361', '362'])).
% 3.74/3.95  
% 3.74/3.95  % SZS output end Refutation
% 3.74/3.95  
% 3.74/3.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
