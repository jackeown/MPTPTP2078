%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9IGkA15Z2U

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:10 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  410 (5604 expanded)
%              Number of leaves         :   47 (1642 expanded)
%              Depth                    :   37
%              Number of atoms          : 4270 (125753 expanded)
%              Number of equality atoms :  230 (4114 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('37',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('63',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
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
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X30 ) @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('144',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('145',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k7_relset_1 @ X15 @ X16 @ X17 @ X15 )
        = ( k2_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k7_relset_1 @ X8 @ X9 @ X7 @ X10 )
        = ( k9_relat_1 @ X7 @ X10 ) ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X2 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('158',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('161',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k7_relset_1 @ X15 @ X16 @ X17 @ X15 )
        = ( k2_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('173',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('175',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k7_relset_1 @ X8 @ X9 @ X7 @ X10 )
        = ( k9_relat_1 @ X7 @ X10 ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('185',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','186','187','188'])).

thf('190',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','189'])).

thf('191',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('192',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('193',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('195',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('196',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('198',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['196','199'])).

thf('201',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['193','200'])).

thf('202',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('203',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('204',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('208',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('209',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X2 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
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
    inference('sup-',[status(thm)],['207','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
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
    inference('sup-',[status(thm)],['206','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
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
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['205','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('218',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('219',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['217','219'])).

thf('221',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('222',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('223',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['220','223'])).

thf('225',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('226',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('227',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('228',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X30 ) @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('229',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('232',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233'])).

thf('235',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['226','234'])).

thf('236',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('240',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('242',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k8_relset_1 @ X15 @ X16 @ X17 @ X16 )
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('243',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('245',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['243','246'])).

thf('248',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['240','247'])).

thf('249',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['225','248'])).

thf('250',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['224','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['216','252'])).

thf('254',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('255',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k7_relset_1 @ X15 @ X16 @ X17 @ X15 )
        = ( k2_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('256',plain,
    ( ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('258',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k7_relset_1 @ X8 @ X9 @ X7 @ X10 )
        = ( k9_relat_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('261',plain,
    ( ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['256','259','260'])).

thf('262',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('263',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['253','261','262','263','264'])).

thf('266',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('271',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(clc,[status(thm)],['269','272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['204','275'])).

thf('277',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','276'])).

thf('278',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','277'])).

thf('279',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','278'])).

thf('280',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['143','280'])).

thf('282',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('283',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['281','282','283','284'])).

thf('286',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('287',plain,(
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

thf('288',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_funct_2 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['289','290','291'])).

thf('293',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('294',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('295',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['292','293','294','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_C = X0 )
      | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['286','296'])).

thf('298',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_C = X0 )
      | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['285','299'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('302',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('303',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X30 ) @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('304',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('306',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['237'])).

thf('307',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['304','305','306'])).

thf('308',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('309',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('310',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['308','309'])).

thf('311',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','186','187','188'])).

thf('312',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','276'])).

thf('314',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['312','313'])).

thf('315',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['307','314'])).

thf('316',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['301','316'])).

thf('318',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('319',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['317','318','319','320'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('323',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('324',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('325',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('327',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('328',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('329',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','189'])).

thf('330',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','276'])).

thf('332',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['322','333'])).

thf('335',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('336',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['334','335','336','337'])).

thf('339',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['300','321','338'])).

thf('340',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['142','339'])).

thf('341',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('342',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_funct_2 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('343',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_funct_2 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['341','343'])).

thf('345',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('346',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['344','345','346'])).

thf('348',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('349',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['340','347','348','349','350'])).

thf('352',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','277'])).

thf('353',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','351','352'])).

thf('354',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['353'])).

thf('355',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['111','354'])).

thf('356',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['184','185'])).

thf('357',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('358',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['355','356','357','358'])).

thf('360',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['344','345','346'])).

thf('361',plain,(
    $false ),
    inference(demod,[status(thm)],['110','359','360'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9IGkA15Z2U
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.77/3.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.77/3.94  % Solved by: fo/fo7.sh
% 3.77/3.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.77/3.94  % done 1183 iterations in 3.472s
% 3.77/3.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.77/3.94  % SZS output start Refutation
% 3.77/3.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.77/3.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.77/3.94  thf(sk_C_type, type, sk_C: $i).
% 3.77/3.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.77/3.94  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.77/3.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.77/3.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.77/3.94  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 3.77/3.94  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.77/3.94  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.77/3.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.77/3.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.77/3.94  thf(sk_A_type, type, sk_A: $i).
% 3.77/3.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.77/3.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.77/3.94  thf(sk_B_type, type, sk_B: $i).
% 3.77/3.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.77/3.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.77/3.94  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.77/3.94  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.77/3.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.77/3.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.77/3.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.77/3.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.77/3.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.77/3.94  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.77/3.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.77/3.94  thf(d3_struct_0, axiom,
% 3.77/3.94    (![A:$i]:
% 3.77/3.94     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.77/3.94  thf('0', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('1', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('2', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf(t64_tops_2, conjecture,
% 3.77/3.94    (![A:$i]:
% 3.77/3.94     ( ( l1_struct_0 @ A ) =>
% 3.77/3.94       ( ![B:$i]:
% 3.77/3.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.77/3.94           ( ![C:$i]:
% 3.77/3.94             ( ( ( v1_funct_1 @ C ) & 
% 3.77/3.94                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.77/3.94                 ( m1_subset_1 @
% 3.77/3.94                   C @ 
% 3.77/3.94                   ( k1_zfmisc_1 @
% 3.77/3.94                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.77/3.94               ( ( ( ( k2_relset_1 @
% 3.77/3.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.77/3.94                     ( k2_struct_0 @ B ) ) & 
% 3.77/3.94                   ( v2_funct_1 @ C ) ) =>
% 3.77/3.94                 ( r2_funct_2 @
% 3.77/3.94                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.77/3.94                   ( k2_tops_2 @
% 3.77/3.94                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.77/3.94                     ( k2_tops_2 @
% 3.77/3.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.77/3.94                   C ) ) ) ) ) ) ))).
% 3.77/3.94  thf(zf_stmt_0, negated_conjecture,
% 3.77/3.94    (~( ![A:$i]:
% 3.77/3.94        ( ( l1_struct_0 @ A ) =>
% 3.77/3.94          ( ![B:$i]:
% 3.77/3.94            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.77/3.94              ( ![C:$i]:
% 3.77/3.94                ( ( ( v1_funct_1 @ C ) & 
% 3.77/3.94                    ( v1_funct_2 @
% 3.77/3.94                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.77/3.94                    ( m1_subset_1 @
% 3.77/3.94                      C @ 
% 3.77/3.94                      ( k1_zfmisc_1 @
% 3.77/3.94                        ( k2_zfmisc_1 @
% 3.77/3.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.77/3.94                  ( ( ( ( k2_relset_1 @
% 3.77/3.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.77/3.94                        ( k2_struct_0 @ B ) ) & 
% 3.77/3.94                      ( v2_funct_1 @ C ) ) =>
% 3.77/3.94                    ( r2_funct_2 @
% 3.77/3.94                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.77/3.94                      ( k2_tops_2 @
% 3.77/3.94                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.77/3.94                        ( k2_tops_2 @
% 3.77/3.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.77/3.94                      C ) ) ) ) ) ) ) )),
% 3.77/3.94    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 3.77/3.94  thf('3', plain,
% 3.77/3.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.77/3.94          sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('4', plain,
% 3.77/3.94      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.77/3.94           sk_C)
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup-', [status(thm)], ['2', '3'])).
% 3.77/3.94  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('6', plain,
% 3.77/3.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.77/3.94          sk_C)),
% 3.77/3.94      inference('demod', [status(thm)], ['4', '5'])).
% 3.77/3.94  thf('7', plain,
% 3.77/3.94      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.77/3.94           sk_C)
% 3.77/3.94        | ~ (l1_struct_0 @ sk_A))),
% 3.77/3.94      inference('sup-', [status(thm)], ['1', '6'])).
% 3.77/3.94  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('9', plain,
% 3.77/3.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.77/3.94          sk_C)),
% 3.77/3.94      inference('demod', [status(thm)], ['7', '8'])).
% 3.77/3.94  thf(d1_funct_2, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i]:
% 3.77/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.77/3.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.77/3.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.77/3.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.77/3.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.77/3.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.77/3.94  thf(zf_stmt_1, axiom,
% 3.77/3.94    (![B:$i,A:$i]:
% 3.77/3.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.77/3.94       ( zip_tseitin_0 @ B @ A ) ))).
% 3.77/3.94  thf('10', plain,
% 3.77/3.94      (![X18 : $i, X19 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.77/3.94  thf('11', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.77/3.94  thf(zf_stmt_3, axiom,
% 3.77/3.94    (![C:$i,B:$i,A:$i]:
% 3.77/3.94     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.77/3.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.77/3.94  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.77/3.94  thf(zf_stmt_5, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i]:
% 3.77/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.94       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.77/3.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.77/3.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.77/3.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.77/3.94  thf('12', plain,
% 3.77/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.77/3.94         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.77/3.94          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.77/3.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.77/3.94  thf('13', plain,
% 3.77/3.94      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.77/3.94        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['11', '12'])).
% 3.77/3.94  thf('14', plain,
% 3.77/3.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.77/3.94        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['10', '13'])).
% 3.77/3.94  thf('15', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('16', plain,
% 3.77/3.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.94         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 3.77/3.94          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 3.77/3.94          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.77/3.94  thf('17', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.77/3.94        | ((u1_struct_0 @ sk_A)
% 3.77/3.94            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['15', '16'])).
% 3.77/3.94  thf('18', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf(t38_relset_1, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i]:
% 3.77/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.94       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 3.77/3.94         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.77/3.94  thf('19', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 3.77/3.94            = (k1_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('20', plain,
% 3.77/3.94      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94         (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['18', '19'])).
% 3.77/3.94  thf('21', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf(redefinition_k8_relset_1, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.94       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 3.77/3.94  thf('22', plain,
% 3.77/3.94      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 3.77/3.94          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.77/3.94  thf('23', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['21', '22'])).
% 3.77/3.94  thf('24', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['20', '23'])).
% 3.77/3.94  thf('25', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.77/3.94        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['17', '24'])).
% 3.77/3.94  thf('26', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('27', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['20', '23'])).
% 3.77/3.94  thf('28', plain,
% 3.77/3.94      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.77/3.94          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup+', [status(thm)], ['26', '27'])).
% 3.77/3.94  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('30', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['28', '29'])).
% 3.77/3.94  thf('31', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('32', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('33', plain,
% 3.77/3.94      (((m1_subset_1 @ sk_C @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup+', [status(thm)], ['31', '32'])).
% 3.77/3.94  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('35', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['33', '34'])).
% 3.77/3.94  thf('36', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 3.77/3.94            = (k1_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('37', plain,
% 3.77/3.94      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94         (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['35', '36'])).
% 3.77/3.94  thf('38', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['33', '34'])).
% 3.77/3.94  thf('39', plain,
% 3.77/3.94      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 3.77/3.94          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.77/3.94  thf('40', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['38', '39'])).
% 3.77/3.94  thf('41', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['37', '40'])).
% 3.77/3.94  thf('42', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup+', [status(thm)], ['30', '41'])).
% 3.77/3.94  thf('43', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.77/3.94        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['25', '42'])).
% 3.77/3.94  thf('44', plain,
% 3.77/3.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.77/3.94        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['14', '43'])).
% 3.77/3.94  thf('45', plain,
% 3.77/3.94      (![X18 : $i, X19 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.77/3.94  thf('46', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('47', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('48', plain,
% 3.77/3.94      (((m1_subset_1 @ sk_C @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_A))),
% 3.77/3.94      inference('sup+', [status(thm)], ['46', '47'])).
% 3.77/3.94  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('50', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('51', plain,
% 3.77/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.77/3.94         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.77/3.94          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.77/3.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.77/3.94  thf('52', plain,
% 3.77/3.94      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['50', '51'])).
% 3.77/3.94  thf('53', plain,
% 3.77/3.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.77/3.94        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['45', '52'])).
% 3.77/3.94  thf('54', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('55', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('56', plain,
% 3.77/3.94      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_A))),
% 3.77/3.94      inference('sup+', [status(thm)], ['54', '55'])).
% 3.77/3.94  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('58', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['56', '57'])).
% 3.77/3.94  thf('59', plain,
% 3.77/3.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.94         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 3.77/3.94          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 3.77/3.94          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.77/3.94  thf('60', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_A)
% 3.77/3.94            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['58', '59'])).
% 3.77/3.94  thf('61', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('62', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 3.77/3.94            = (k1_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('63', plain,
% 3.77/3.94      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94         (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['61', '62'])).
% 3.77/3.94  thf('64', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('65', plain,
% 3.77/3.94      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 3.77/3.94          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.77/3.94  thf('66', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['64', '65'])).
% 3.77/3.94  thf('67', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['63', '66'])).
% 3.77/3.94  thf('68', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['60', '67'])).
% 3.77/3.94  thf('69', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup+', [status(thm)], ['30', '41'])).
% 3.77/3.94  thf('70', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['68', '69'])).
% 3.77/3.94  thf('71', plain,
% 3.77/3.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['53', '70'])).
% 3.77/3.94  thf('72', plain,
% 3.77/3.94      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 3.77/3.94        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.77/3.94        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 3.77/3.94      inference('sup+', [status(thm)], ['44', '71'])).
% 3.77/3.94  thf('73', plain,
% 3.77/3.94      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 3.77/3.94      inference('simplify', [status(thm)], ['72'])).
% 3.77/3.94  thf(fc2_struct_0, axiom,
% 3.77/3.94    (![A:$i]:
% 3.77/3.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.77/3.94       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.77/3.94  thf('74', plain,
% 3.77/3.94      (![X34 : $i]:
% 3.77/3.94         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 3.77/3.94          | ~ (l1_struct_0 @ X34)
% 3.77/3.94          | (v2_struct_0 @ X34))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.77/3.94  thf('75', plain,
% 3.77/3.94      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.77/3.94        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 3.77/3.94        | (v2_struct_0 @ sk_B)
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup-', [status(thm)], ['73', '74'])).
% 3.77/3.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.77/3.94  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.77/3.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.77/3.94  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('78', plain,
% 3.77/3.94      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.77/3.94  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('80', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.77/3.94      inference('clc', [status(thm)], ['78', '79'])).
% 3.77/3.94  thf('81', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.77/3.94      inference('clc', [status(thm)], ['78', '79'])).
% 3.77/3.94  thf('82', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('83', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('84', plain,
% 3.77/3.94      (((m1_subset_1 @ sk_C @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup+', [status(thm)], ['82', '83'])).
% 3.77/3.94  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('86', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf(d4_tops_2, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i]:
% 3.77/3.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.94       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.77/3.94         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.77/3.94  thf('87', plain,
% 3.77/3.94      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.77/3.94         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 3.77/3.94          | ~ (v2_funct_1 @ X37)
% 3.77/3.94          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 3.77/3.94          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 3.77/3.94          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 3.77/3.94          | ~ (v1_funct_1 @ X37))),
% 3.77/3.94      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.77/3.94  thf('88', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.77/3.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            = (k2_funct_1 @ sk_C))
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            != (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['86', '87'])).
% 3.77/3.94  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('90', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('91', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['56', '57'])).
% 3.77/3.94  thf('92', plain,
% 3.77/3.94      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup+', [status(thm)], ['90', '91'])).
% 3.77/3.94  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('94', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['92', '93'])).
% 3.77/3.94  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('96', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('97', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('98', plain,
% 3.77/3.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('99', plain,
% 3.77/3.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94          = (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_A))),
% 3.77/3.94      inference('sup+', [status(thm)], ['97', '98'])).
% 3.77/3.94  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('101', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['99', '100'])).
% 3.77/3.94  thf('102', plain,
% 3.77/3.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94          = (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup+', [status(thm)], ['96', '101'])).
% 3.77/3.94  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('104', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['102', '103'])).
% 3.77/3.94  thf('105', plain,
% 3.77/3.94      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94          = (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['88', '89', '94', '95', '104'])).
% 3.77/3.94  thf('106', plain,
% 3.77/3.94      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_funct_1 @ sk_C))),
% 3.77/3.94      inference('simplify', [status(thm)], ['105'])).
% 3.77/3.94  thf('107', plain,
% 3.77/3.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94          sk_C)),
% 3.77/3.94      inference('demod', [status(thm)], ['9', '80', '81', '106'])).
% 3.77/3.94  thf('108', plain,
% 3.77/3.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           sk_C)
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup-', [status(thm)], ['0', '107'])).
% 3.77/3.94  thf('109', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('110', plain,
% 3.77/3.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94          sk_C)),
% 3.77/3.94      inference('demod', [status(thm)], ['108', '109'])).
% 3.77/3.94  thf(fc6_funct_1, axiom,
% 3.77/3.94    (![A:$i]:
% 3.77/3.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.77/3.94       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.77/3.94         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.77/3.94         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.77/3.94  thf('111', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('112', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf(t31_funct_2, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i]:
% 3.77/3.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.94       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.77/3.94         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.77/3.94           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.77/3.94           ( m1_subset_1 @
% 3.77/3.94             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.77/3.94  thf('113', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (m1_subset_1 @ (k2_funct_1 @ X30) @ 
% 3.77/3.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('114', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            != (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['112', '113'])).
% 3.77/3.94  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('116', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['92', '93'])).
% 3.77/3.94  thf('117', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['102', '103'])).
% 3.77/3.94  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('119', plain,
% 3.77/3.94      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.77/3.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 3.77/3.94  thf('120', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['119'])).
% 3.77/3.94  thf('121', plain,
% 3.77/3.94      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.77/3.94         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 3.77/3.94          | ~ (v2_funct_1 @ X37)
% 3.77/3.94          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 3.77/3.94          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 3.77/3.94          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 3.77/3.94          | ~ (v1_funct_1 @ X37))),
% 3.77/3.94      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.77/3.94  thf('122', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94             (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['120', '121'])).
% 3.77/3.94  thf('123', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf('124', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (v1_funct_1 @ (k2_funct_1 @ X30))
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('125', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.77/3.94        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            != (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['123', '124'])).
% 3.77/3.94  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('127', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['92', '93'])).
% 3.77/3.94  thf('128', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['102', '103'])).
% 3.77/3.94  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('130', plain,
% 3.77/3.94      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 3.77/3.94  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.77/3.94      inference('simplify', [status(thm)], ['130'])).
% 3.77/3.94  thf('132', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf('133', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (v1_funct_2 @ (k2_funct_1 @ X30) @ X31 @ X32)
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('134', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            != (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['132', '133'])).
% 3.77/3.94  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('136', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['92', '93'])).
% 3.77/3.94  thf('137', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['102', '103'])).
% 3.77/3.94  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('139', plain,
% 3.77/3.94      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94         (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 3.77/3.94  thf('140', plain,
% 3.77/3.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94        (k2_struct_0 @ sk_A))),
% 3.77/3.94      inference('simplify', [status(thm)], ['139'])).
% 3.77/3.94  thf('141', plain,
% 3.77/3.94      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('demod', [status(thm)], ['122', '131', '140'])).
% 3.77/3.94  thf(t65_funct_1, axiom,
% 3.77/3.94    (![A:$i]:
% 3.77/3.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.77/3.94       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.77/3.94  thf('142', plain,
% 3.77/3.94      (![X3 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X3)
% 3.77/3.94          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.77/3.94          | ~ (v1_funct_1 @ X3)
% 3.77/3.94          | ~ (v1_relat_1 @ X3))),
% 3.77/3.94      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.77/3.94  thf('143', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('144', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['119'])).
% 3.77/3.94  thf('145', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (m1_subset_1 @ (k2_funct_1 @ X30) @ 
% 3.77/3.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('146', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94             (k2_struct_0 @ sk_A))
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['144', '145'])).
% 3.77/3.94  thf('147', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.77/3.94      inference('simplify', [status(thm)], ['130'])).
% 3.77/3.94  thf('148', plain,
% 3.77/3.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94        (k2_struct_0 @ sk_A))),
% 3.77/3.94      inference('simplify', [status(thm)], ['139'])).
% 3.77/3.94  thf('149', plain,
% 3.77/3.94      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['146', '147', '148'])).
% 3.77/3.94  thf('150', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['119'])).
% 3.77/3.94  thf('151', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k7_relset_1 @ X15 @ X16 @ X17 @ X15)
% 3.77/3.94            = (k2_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('152', plain,
% 3.77/3.94      (((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94         (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['150', '151'])).
% 3.77/3.94  thf('153', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['119'])).
% 3.77/3.94  thf(redefinition_k7_relset_1, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.94       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 3.77/3.94  thf('154', plain,
% 3.77/3.94      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 3.77/3.94          | ((k7_relset_1 @ X8 @ X9 @ X7 @ X10) = (k9_relat_1 @ X7 @ X10)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.77/3.94  thf('155', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_funct_1 @ sk_C) @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['153', '154'])).
% 3.77/3.94  thf('156', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['152', '155'])).
% 3.77/3.94  thf(t155_funct_1, axiom,
% 3.77/3.94    (![A:$i,B:$i]:
% 3.77/3.94     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.77/3.94       ( ( v2_funct_1 @ B ) =>
% 3.77/3.94         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 3.77/3.94  thf('157', plain,
% 3.77/3.94      (![X1 : $i, X2 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X1)
% 3.77/3.94          | ((k10_relat_1 @ X1 @ X2) = (k9_relat_1 @ (k2_funct_1 @ X1) @ X2))
% 3.77/3.94          | ~ (v1_funct_1 @ X1)
% 3.77/3.94          | ~ (v1_relat_1 @ X1))),
% 3.77/3.94      inference('cnf', [status(esa)], [t155_funct_1])).
% 3.77/3.94  thf('158', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('159', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('160', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('161', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (m1_subset_1 @ (k2_funct_1 @ X30) @ 
% 3.77/3.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('162', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            != (u1_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['160', '161'])).
% 3.77/3.94  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('164', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['56', '57'])).
% 3.77/3.94  thf('165', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['99', '100'])).
% 3.77/3.94  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('167', plain,
% 3.77/3.94      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.77/3.94        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 3.77/3.94  thf('168', plain,
% 3.77/3.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B)
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['159', '167'])).
% 3.77/3.94  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('170', plain,
% 3.77/3.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 3.77/3.94      inference('demod', [status(thm)], ['168', '169'])).
% 3.77/3.94  thf('171', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['170'])).
% 3.77/3.94  thf('172', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k7_relset_1 @ X15 @ X16 @ X17 @ X15)
% 3.77/3.94            = (k2_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('173', plain,
% 3.77/3.94      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94         (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['171', '172'])).
% 3.77/3.94  thf('174', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['170'])).
% 3.77/3.94  thf('175', plain,
% 3.77/3.94      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 3.77/3.94          | ((k7_relset_1 @ X8 @ X9 @ X7 @ X10) = (k9_relat_1 @ X7 @ X10)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.77/3.94  thf('176', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_funct_1 @ sk_C) @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['174', '175'])).
% 3.77/3.94  thf('177', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['173', '176'])).
% 3.77/3.94  thf('178', plain,
% 3.77/3.94      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.77/3.94          = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94             (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup+', [status(thm)], ['158', '177'])).
% 3.77/3.94  thf('179', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['152', '155'])).
% 3.77/3.94  thf('180', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('181', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['178', '179', '180'])).
% 3.77/3.94  thf('182', plain,
% 3.77/3.94      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.77/3.94          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))
% 3.77/3.94        | ~ (v1_relat_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.94      inference('sup+', [status(thm)], ['157', '181'])).
% 3.77/3.94  thf('183', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup+', [status(thm)], ['30', '41'])).
% 3.77/3.94  thf('184', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf(cc1_relset_1, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i]:
% 3.77/3.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.94       ( v1_relat_1 @ C ) ))).
% 3.77/3.94  thf('185', plain,
% 3.77/3.94      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.77/3.94         ((v1_relat_1 @ X4)
% 3.77/3.94          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 3.77/3.94      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.77/3.94  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('189', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['182', '183', '186', '187', '188'])).
% 3.77/3.94  thf('190', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['156', '189'])).
% 3.77/3.94  thf('191', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['92', '93'])).
% 3.77/3.94  thf('192', plain,
% 3.77/3.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.94         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 3.77/3.94          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 3.77/3.94          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.77/3.94  thf('193', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_A)
% 3.77/3.94            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['191', '192'])).
% 3.77/3.94  thf('194', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf('195', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 3.77/3.94            = (k1_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('196', plain,
% 3.77/3.94      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94         (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['194', '195'])).
% 3.77/3.94  thf('197', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf('198', plain,
% 3.77/3.94      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 3.77/3.94          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.77/3.94  thf('199', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['197', '198'])).
% 3.77/3.94  thf('200', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['196', '199'])).
% 3.77/3.94  thf('201', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['193', '200'])).
% 3.77/3.94  thf('202', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['84', '85'])).
% 3.77/3.94  thf('203', plain,
% 3.77/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.77/3.94         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.77/3.94          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.77/3.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.77/3.94  thf('204', plain,
% 3.77/3.94      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['202', '203'])).
% 3.77/3.94  thf('205', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('206', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('207', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('208', plain,
% 3.77/3.94      (![X3 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X3)
% 3.77/3.94          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.77/3.94          | ~ (v1_funct_1 @ X3)
% 3.77/3.94          | ~ (v1_relat_1 @ X3))),
% 3.77/3.94      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.77/3.94  thf('209', plain,
% 3.77/3.94      (![X1 : $i, X2 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X1)
% 3.77/3.94          | ((k10_relat_1 @ X1 @ X2) = (k9_relat_1 @ (k2_funct_1 @ X1) @ X2))
% 3.77/3.94          | ~ (v1_funct_1 @ X1)
% 3.77/3.94          | ~ (v1_relat_1 @ X1))),
% 3.77/3.94      inference('cnf', [status(esa)], [t155_funct_1])).
% 3.77/3.94  thf('210', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.77/3.94          | ~ (v1_relat_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.77/3.94      inference('sup+', [status(thm)], ['208', '209'])).
% 3.77/3.94  thf('211', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (~ (v1_relat_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0)
% 3.77/3.94          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['207', '210'])).
% 3.77/3.94  thf('212', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.77/3.94          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('simplify', [status(thm)], ['211'])).
% 3.77/3.94  thf('213', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (~ (v1_relat_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['206', '212'])).
% 3.77/3.94  thf('214', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.77/3.94          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('simplify', [status(thm)], ['213'])).
% 3.77/3.94  thf('215', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (~ (v1_relat_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['205', '214'])).
% 3.77/3.94  thf('216', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]:
% 3.77/3.94         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('simplify', [status(thm)], ['215'])).
% 3.77/3.94  thf('217', plain,
% 3.77/3.94      (![X18 : $i, X19 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.77/3.94  thf('218', plain,
% 3.77/3.94      (![X18 : $i, X19 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.77/3.94  thf('219', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 3.77/3.94      inference('simplify', [status(thm)], ['218'])).
% 3.77/3.94  thf('220', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.77/3.94      inference('sup+', [status(thm)], ['217', '219'])).
% 3.77/3.94  thf('221', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['119'])).
% 3.77/3.94  thf('222', plain,
% 3.77/3.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.77/3.94         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.77/3.94          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.77/3.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.77/3.94  thf('223', plain,
% 3.77/3.94      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94         (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['221', '222'])).
% 3.77/3.94  thf('224', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.77/3.94          | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94             (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['220', '223'])).
% 3.77/3.94  thf('225', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('226', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('227', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('228', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (v1_funct_2 @ (k2_funct_1 @ X30) @ X31 @ X32)
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('229', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94            != (u1_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['227', '228'])).
% 3.77/3.94  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('231', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['56', '57'])).
% 3.77/3.94  thf('232', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['99', '100'])).
% 3.77/3.94  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('234', plain,
% 3.77/3.94      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94         (k2_struct_0 @ sk_A))
% 3.77/3.94        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['229', '230', '231', '232', '233'])).
% 3.77/3.94  thf('235', plain,
% 3.77/3.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B)
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['226', '234'])).
% 3.77/3.94  thf('236', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('237', plain,
% 3.77/3.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('demod', [status(thm)], ['235', '236'])).
% 3.77/3.94  thf('238', plain,
% 3.77/3.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94        (k2_struct_0 @ sk_A))),
% 3.77/3.94      inference('simplify', [status(thm)], ['237'])).
% 3.77/3.94  thf('239', plain,
% 3.77/3.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.94         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 3.77/3.94          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 3.77/3.94          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.77/3.94  thf('240', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (u1_struct_0 @ sk_B))
% 3.77/3.94        | ((u1_struct_0 @ sk_B)
% 3.77/3.94            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94               (k2_funct_1 @ sk_C))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['238', '239'])).
% 3.77/3.94  thf('241', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['170'])).
% 3.77/3.94  thf('242', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k8_relset_1 @ X15 @ X16 @ X17 @ X16)
% 3.77/3.94            = (k1_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('243', plain,
% 3.77/3.94      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94         (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['241', '242'])).
% 3.77/3.94  thf('244', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['170'])).
% 3.77/3.94  thf('245', plain,
% 3.77/3.94      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 3.77/3.94          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.77/3.94  thf('246', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['244', '245'])).
% 3.77/3.94  thf('247', plain,
% 3.77/3.94      (((k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 3.77/3.94         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['243', '246'])).
% 3.77/3.94  thf('248', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (u1_struct_0 @ sk_B))
% 3.77/3.94        | ((u1_struct_0 @ sk_B)
% 3.77/3.94            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('demod', [status(thm)], ['240', '247'])).
% 3.77/3.94  thf('249', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_struct_0 @ sk_B))
% 3.77/3.94        | ~ (l1_struct_0 @ sk_B)
% 3.77/3.94        | ((u1_struct_0 @ sk_B)
% 3.77/3.94            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['225', '248'])).
% 3.77/3.94  thf('250', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('251', plain,
% 3.77/3.94      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94           (k2_struct_0 @ sk_B))
% 3.77/3.94        | ((u1_struct_0 @ sk_B)
% 3.77/3.94            = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('demod', [status(thm)], ['249', '250'])).
% 3.77/3.94  thf('252', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.77/3.94          | ((u1_struct_0 @ sk_B)
% 3.77/3.94              = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['224', '251'])).
% 3.77/3.94  thf('253', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (((u1_struct_0 @ sk_B) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 3.77/3.94          | ~ (v1_relat_1 @ sk_C)
% 3.77/3.94          | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94          | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 3.77/3.94      inference('sup+', [status(thm)], ['216', '252'])).
% 3.77/3.94  thf('254', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('255', plain,
% 3.77/3.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.77/3.94         (((k7_relset_1 @ X15 @ X16 @ X17 @ X15)
% 3.77/3.94            = (k2_relset_1 @ X15 @ X16 @ X17))
% 3.77/3.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.77/3.94      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.77/3.94  thf('256', plain,
% 3.77/3.94      (((k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94         (k2_struct_0 @ sk_A))
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['254', '255'])).
% 3.77/3.94  thf('257', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('258', plain,
% 3.77/3.94      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 3.77/3.94          | ((k7_relset_1 @ X8 @ X9 @ X7 @ X10) = (k9_relat_1 @ X7 @ X10)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.77/3.94  thf('259', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           X0) = (k9_relat_1 @ sk_C @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['257', '258'])).
% 3.77/3.94  thf('260', plain,
% 3.77/3.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.77/3.94         = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['99', '100'])).
% 3.77/3.94  thf('261', plain,
% 3.77/3.94      (((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['256', '259', '260'])).
% 3.77/3.94  thf('262', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('263', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('264', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('265', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))
% 3.77/3.94          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 3.77/3.94      inference('demod', [status(thm)], ['253', '261', '262', '263', '264'])).
% 3.77/3.94  thf('266', plain,
% 3.77/3.94      (![X34 : $i]:
% 3.77/3.94         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 3.77/3.94          | ~ (l1_struct_0 @ X34)
% 3.77/3.94          | (v2_struct_0 @ X34))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.77/3.94  thf('267', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.77/3.94          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.77/3.94          | (v2_struct_0 @ sk_B)
% 3.77/3.94          | ~ (l1_struct_0 @ sk_B))),
% 3.77/3.94      inference('sup-', [status(thm)], ['265', '266'])).
% 3.77/3.94  thf('268', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('269', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.77/3.94          | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)
% 3.77/3.94          | (v2_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['267', '268'])).
% 3.77/3.94  thf('270', plain,
% 3.77/3.94      (![X18 : $i, X19 : $i]:
% 3.77/3.94         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.77/3.94  thf('271', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.77/3.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.77/3.94  thf('272', plain,
% 3.77/3.94      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.77/3.94      inference('sup+', [status(thm)], ['270', '271'])).
% 3.77/3.94  thf('273', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v2_struct_0 @ sk_B) | (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 3.77/3.94      inference('clc', [status(thm)], ['269', '272'])).
% 3.77/3.94  thf('274', plain, (~ (v2_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('275', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ X0)),
% 3.77/3.94      inference('clc', [status(thm)], ['273', '274'])).
% 3.77/3.94  thf('276', plain,
% 3.77/3.94      ((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 3.77/3.94      inference('demod', [status(thm)], ['204', '275'])).
% 3.77/3.94  thf('277', plain,
% 3.77/3.94      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['201', '276'])).
% 3.77/3.94  thf('278', plain,
% 3.77/3.94      (((k2_struct_0 @ sk_A)
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['190', '277'])).
% 3.77/3.94  thf('279', plain,
% 3.77/3.94      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94         (k1_zfmisc_1 @ 
% 3.77/3.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['149', '278'])).
% 3.77/3.94  thf('280', plain,
% 3.77/3.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['279'])).
% 3.77/3.94  thf('281', plain,
% 3.77/3.94      ((~ (v1_relat_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           (k1_zfmisc_1 @ 
% 3.77/3.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['143', '280'])).
% 3.77/3.94  thf('282', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('283', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('284', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('285', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['281', '282', '283', '284'])).
% 3.77/3.94  thf('286', plain,
% 3.77/3.94      (![X33 : $i]:
% 3.77/3.94         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.77/3.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.77/3.94  thf('287', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf(redefinition_r2_funct_2, axiom,
% 3.77/3.94    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.94         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.77/3.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.94       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.77/3.94  thf('288', plain,
% 3.77/3.94      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.77/3.94          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 3.77/3.94          | ~ (v1_funct_1 @ X26)
% 3.77/3.94          | ~ (v1_funct_1 @ X29)
% 3.77/3.94          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.77/3.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.77/3.94          | ((X26) = (X29))
% 3.77/3.94          | ~ (r2_funct_2 @ X27 @ X28 @ X26 @ X29))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.77/3.94  thf('289', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94             X0)
% 3.77/3.94          | ((sk_C) = (X0))
% 3.77/3.94          | ~ (m1_subset_1 @ X0 @ 
% 3.77/3.94               (k1_zfmisc_1 @ 
% 3.77/3.94                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.77/3.94          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['287', '288'])).
% 3.77/3.94  thf('290', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('291', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('292', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94             X0)
% 3.77/3.94          | ((sk_C) = (X0))
% 3.77/3.94          | ~ (m1_subset_1 @ X0 @ 
% 3.77/3.94               (k1_zfmisc_1 @ 
% 3.77/3.94                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.77/3.94          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94          | ~ (v1_funct_1 @ X0))),
% 3.77/3.94      inference('demod', [status(thm)], ['289', '290', '291'])).
% 3.77/3.94  thf('293', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.77/3.94      inference('clc', [status(thm)], ['78', '79'])).
% 3.77/3.94  thf('294', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.77/3.94      inference('clc', [status(thm)], ['78', '79'])).
% 3.77/3.94  thf('295', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.77/3.94      inference('clc', [status(thm)], ['78', '79'])).
% 3.77/3.94  thf('296', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94             X0)
% 3.77/3.94          | ((sk_C) = (X0))
% 3.77/3.94          | ~ (m1_subset_1 @ X0 @ 
% 3.77/3.94               (k1_zfmisc_1 @ 
% 3.77/3.94                (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.77/3.94          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94          | ~ (v1_funct_1 @ X0))),
% 3.77/3.94      inference('demod', [status(thm)], ['292', '293', '294', '295'])).
% 3.77/3.94  thf('297', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X0 @ 
% 3.77/3.94             (k1_zfmisc_1 @ 
% 3.77/3.94              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94          | ~ (l1_struct_0 @ sk_B)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94          | ((sk_C) = (X0))
% 3.77/3.94          | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94               sk_C @ X0))),
% 3.77/3.94      inference('sup-', [status(thm)], ['286', '296'])).
% 3.77/3.94  thf('298', plain, ((l1_struct_0 @ sk_B)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('299', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X0 @ 
% 3.77/3.94             (k1_zfmisc_1 @ 
% 3.77/3.94              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94          | ((sk_C) = (X0))
% 3.77/3.94          | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94               sk_C @ X0))),
% 3.77/3.94      inference('demod', [status(thm)], ['297', '298'])).
% 3.77/3.94  thf('300', plain,
% 3.77/3.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94             (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['285', '299'])).
% 3.77/3.94  thf('301', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('302', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['170'])).
% 3.77/3.94  thf('303', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (v1_funct_2 @ (k2_funct_1 @ X30) @ X31 @ X32)
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('304', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94             (k2_struct_0 @ sk_A))
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['302', '303'])).
% 3.77/3.94  thf('305', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.77/3.94      inference('simplify', [status(thm)], ['130'])).
% 3.77/3.94  thf('306', plain,
% 3.77/3.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.77/3.94        (k2_struct_0 @ sk_A))),
% 3.77/3.94      inference('simplify', [status(thm)], ['237'])).
% 3.77/3.94  thf('307', plain,
% 3.77/3.94      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94         (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['304', '305', '306'])).
% 3.77/3.94  thf('308', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['173', '176'])).
% 3.77/3.94  thf('309', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.77/3.94         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['178', '179', '180'])).
% 3.77/3.94  thf('310', plain,
% 3.77/3.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['308', '309'])).
% 3.77/3.94  thf('311', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['182', '183', '186', '187', '188'])).
% 3.77/3.94  thf('312', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['310', '311'])).
% 3.77/3.94  thf('313', plain,
% 3.77/3.94      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['201', '276'])).
% 3.77/3.94  thf('314', plain,
% 3.77/3.94      (((k2_struct_0 @ sk_A)
% 3.77/3.94         = (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['312', '313'])).
% 3.77/3.94  thf('315', plain,
% 3.77/3.94      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94         (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['307', '314'])).
% 3.77/3.94  thf('316', plain,
% 3.77/3.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('simplify', [status(thm)], ['315'])).
% 3.77/3.94  thf('317', plain,
% 3.77/3.94      ((~ (v1_relat_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['301', '316'])).
% 3.77/3.94  thf('318', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('319', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('320', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('321', plain,
% 3.77/3.94      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.77/3.94        (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['317', '318', '319', '320'])).
% 3.77/3.94  thf('322', plain,
% 3.77/3.94      (![X0 : $i]:
% 3.77/3.94         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.77/3.94          | ~ (v2_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_funct_1 @ X0)
% 3.77/3.94          | ~ (v1_relat_1 @ X0))),
% 3.77/3.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.77/3.94  thf('323', plain,
% 3.77/3.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['119'])).
% 3.77/3.94  thf('324', plain,
% 3.77/3.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.77/3.94         (~ (v2_funct_1 @ X30)
% 3.77/3.94          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 3.77/3.94          | (v1_funct_1 @ (k2_funct_1 @ X30))
% 3.77/3.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.77/3.94          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 3.77/3.94          | ~ (v1_funct_1 @ X30))),
% 3.77/3.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.77/3.94  thf('325', plain,
% 3.77/3.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94             (k2_struct_0 @ sk_A))
% 3.77/3.94        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['323', '324'])).
% 3.77/3.94  thf('326', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.77/3.94      inference('simplify', [status(thm)], ['130'])).
% 3.77/3.94  thf('327', plain,
% 3.77/3.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.77/3.94        (k2_struct_0 @ sk_A))),
% 3.77/3.94      inference('simplify', [status(thm)], ['139'])).
% 3.77/3.94  thf('328', plain,
% 3.77/3.94      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['325', '326', '327'])).
% 3.77/3.94  thf('329', plain,
% 3.77/3.94      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['156', '189'])).
% 3.77/3.94  thf('330', plain,
% 3.77/3.94      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['328', '329'])).
% 3.77/3.94  thf('331', plain,
% 3.77/3.94      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 3.77/3.94      inference('demod', [status(thm)], ['201', '276'])).
% 3.77/3.94  thf('332', plain,
% 3.77/3.94      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['330', '331'])).
% 3.77/3.94  thf('333', plain,
% 3.77/3.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['332'])).
% 3.77/3.94  thf('334', plain,
% 3.77/3.94      ((~ (v1_relat_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['322', '333'])).
% 3.77/3.94  thf('335', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('336', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('337', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('338', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['334', '335', '336', '337'])).
% 3.77/3.94  thf('339', plain,
% 3.77/3.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.77/3.94        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.77/3.94      inference('demod', [status(thm)], ['300', '321', '338'])).
% 3.77/3.94  thf('340', plain,
% 3.77/3.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           sk_C)
% 3.77/3.94        | ~ (v1_relat_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.77/3.94      inference('sup-', [status(thm)], ['142', '339'])).
% 3.77/3.94  thf('341', plain,
% 3.77/3.94      ((m1_subset_1 @ sk_C @ 
% 3.77/3.94        (k1_zfmisc_1 @ 
% 3.77/3.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.77/3.94      inference('demod', [status(thm)], ['48', '49'])).
% 3.77/3.94  thf('342', plain,
% 3.77/3.94      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.77/3.94         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.77/3.94          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 3.77/3.94          | ~ (v1_funct_1 @ X26)
% 3.77/3.94          | ~ (v1_funct_1 @ X29)
% 3.77/3.94          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.77/3.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.77/3.94          | (r2_funct_2 @ X27 @ X28 @ X26 @ X29)
% 3.77/3.94          | ((X26) != (X29)))),
% 3.77/3.94      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.77/3.94  thf('343', plain,
% 3.77/3.94      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.77/3.94         ((r2_funct_2 @ X27 @ X28 @ X29 @ X29)
% 3.77/3.94          | ~ (v1_funct_1 @ X29)
% 3.77/3.94          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.77/3.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.77/3.94      inference('simplify', [status(thm)], ['342'])).
% 3.77/3.94  thf('344', plain,
% 3.77/3.94      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.77/3.94           sk_C))),
% 3.77/3.94      inference('sup-', [status(thm)], ['341', '343'])).
% 3.77/3.94  thf('345', plain,
% 3.77/3.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.77/3.94      inference('demod', [status(thm)], ['56', '57'])).
% 3.77/3.94  thf('346', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('347', plain,
% 3.77/3.94      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 3.77/3.94      inference('demod', [status(thm)], ['344', '345', '346'])).
% 3.77/3.94  thf('348', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('349', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('350', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('351', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['340', '347', '348', '349', '350'])).
% 3.77/3.94  thf('352', plain,
% 3.77/3.94      (((k2_struct_0 @ sk_A)
% 3.77/3.94         = (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)))),
% 3.77/3.94      inference('demod', [status(thm)], ['190', '277'])).
% 3.77/3.94  thf('353', plain,
% 3.77/3.94      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94          (k2_funct_1 @ sk_C)) = (sk_C))
% 3.77/3.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 3.77/3.94      inference('demod', [status(thm)], ['141', '351', '352'])).
% 3.77/3.94  thf('354', plain,
% 3.77/3.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.77/3.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 3.77/3.94      inference('simplify', [status(thm)], ['353'])).
% 3.77/3.94  thf('355', plain,
% 3.77/3.94      ((~ (v1_relat_1 @ sk_C)
% 3.77/3.94        | ~ (v1_funct_1 @ sk_C)
% 3.77/3.94        | ~ (v2_funct_1 @ sk_C)
% 3.77/3.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 3.77/3.94      inference('sup-', [status(thm)], ['111', '354'])).
% 3.77/3.94  thf('356', plain, ((v1_relat_1 @ sk_C)),
% 3.77/3.94      inference('sup-', [status(thm)], ['184', '185'])).
% 3.77/3.94  thf('357', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('358', plain, ((v2_funct_1 @ sk_C)),
% 3.77/3.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.94  thf('359', plain,
% 3.77/3.94      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.77/3.94         (k2_funct_1 @ sk_C)) = (sk_C))),
% 3.77/3.94      inference('demod', [status(thm)], ['355', '356', '357', '358'])).
% 3.77/3.94  thf('360', plain,
% 3.77/3.94      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 3.77/3.94      inference('demod', [status(thm)], ['344', '345', '346'])).
% 3.77/3.94  thf('361', plain, ($false),
% 3.77/3.94      inference('demod', [status(thm)], ['110', '359', '360'])).
% 3.77/3.94  
% 3.77/3.94  % SZS output end Refutation
% 3.77/3.94  
% 3.77/3.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
