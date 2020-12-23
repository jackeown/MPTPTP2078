%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TUe46HDbni

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:24 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  413 (7515 expanded)
%              Number of leaves         :   50 (2202 expanded)
%              Depth                    :   51
%              Number of atoms          : 4108 (163594 expanded)
%              Number of equality atoms :  176 (5099 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('23',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('31',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['36','41','42'])).

thf('44',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('52',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','57'])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','58'])).

thf('60',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','79'])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('89',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','56'])).

thf('90',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','79'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('99',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','94','95','96','97','98'])).

thf('100',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

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

thf('107',plain,(
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

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('112',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('119',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['118','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('129',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','116','117','129'])).

thf('131',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['99','131'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('133',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('134',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
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

thf('135',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('136',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('137',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

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

thf('139',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('149',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('150',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('152',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('153',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('154',plain,(
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

thf('155',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['151','160'])).

thf('162',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['150','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('164',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('165',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('168',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','166','167','168','169'])).

thf('171',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('176',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('181',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('182',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('183',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('184',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('185',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('186',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('187',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['186','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['185','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['184','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['183','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['199','200','201','202'])).

thf('204',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['182','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['181','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('215',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('217',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('220',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('221',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('222',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','222'])).

thf('224',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('225',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('227',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('232',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['215','218','232'])).

thf('234',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','83'])).

thf('235',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('237',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('238',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('239',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['238','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['237','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['236','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['235','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['180','255'])).

thf('257',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('258',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('260',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('261',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('262',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('263',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('264',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('265',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('266',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('267',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('268',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['266','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['265','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['264','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['263','275'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['262','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['261','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['260','280'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['259','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['258','286'])).

thf('288',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('291',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['287','288','289','290'])).

thf('292',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['179','291'])).

thf('293',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('294',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('295',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('296',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('298',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('299',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('301',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['292','293','299','300','301','302'])).

thf('304',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['162','171','172','173','178','303'])).

thf('305',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['137','304'])).

thf('306',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('307',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['305','306','307','308'])).

thf('310',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('311',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['136','311'])).

thf('313',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('314',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['312','313','314','315','316'])).

thf('318',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['135','317'])).

thf('319',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('320',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('321',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['318','319','320'])).

thf('322',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','321'])).

thf('323',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('324',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['322','323','324','325'])).

thf('327',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('328',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('329',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('331',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('332',plain,(
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

thf('333',plain,(
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
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
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
    inference('sup-',[status(thm)],['330','334'])).

thf('336',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['335'])).

thf('337',plain,(
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
    inference('sup-',[status(thm)],['329','336'])).

thf('338',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['326','338'])).

thf('340',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['292','293','299','300','301','302'])).

thf('341',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('342',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('343',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['339','340','341','342'])).

thf('344',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['133','343'])).

thf('345',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('346',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['344','345','346','347'])).

thf('349',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['132','348'])).

thf('350',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','349'])).

thf('351',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

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

thf('352',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_funct_2 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('353',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['351','353'])).

thf('355',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('356',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['354','355','356'])).

thf('358',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('359',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    $false ),
    inference(demod,[status(thm)],['350','357','358','359','360'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TUe46HDbni
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.23/2.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.23/2.42  % Solved by: fo/fo7.sh
% 2.23/2.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.23/2.42  % done 1541 iterations in 1.960s
% 2.23/2.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.23/2.42  % SZS output start Refutation
% 2.23/2.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.23/2.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.23/2.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.23/2.42  thf(sk_A_type, type, sk_A: $i).
% 2.23/2.42  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.23/2.42  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.23/2.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.23/2.42  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.23/2.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.23/2.42  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.23/2.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.23/2.42  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.23/2.42  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.23/2.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.23/2.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.23/2.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.23/2.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.23/2.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.23/2.42  thf(sk_B_type, type, sk_B: $i).
% 2.23/2.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.23/2.42  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.23/2.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.23/2.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.23/2.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.23/2.42  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.23/2.42  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.23/2.42  thf(sk_C_type, type, sk_C: $i).
% 2.23/2.42  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.23/2.42  thf(t65_funct_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.42       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 2.23/2.42  thf('0', plain,
% 2.23/2.42      (![X6 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X6)
% 2.23/2.42          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 2.23/2.42          | ~ (v1_funct_1 @ X6)
% 2.23/2.42          | ~ (v1_relat_1 @ X6))),
% 2.23/2.42      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.23/2.42  thf(d3_struct_0, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.23/2.42  thf('1', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('2', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf(t64_tops_2, conjecture,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( l1_struct_0 @ A ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( ( v1_funct_1 @ C ) & 
% 2.23/2.42                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.23/2.42                 ( m1_subset_1 @
% 2.23/2.42                   C @ 
% 2.23/2.42                   ( k1_zfmisc_1 @
% 2.23/2.42                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.23/2.42               ( ( ( ( k2_relset_1 @
% 2.23/2.42                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.23/2.42                     ( k2_struct_0 @ B ) ) & 
% 2.23/2.42                   ( v2_funct_1 @ C ) ) =>
% 2.23/2.42                 ( r2_funct_2 @
% 2.23/2.42                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 2.23/2.42                   ( k2_tops_2 @
% 2.23/2.42                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.23/2.42                     ( k2_tops_2 @
% 2.23/2.42                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 2.23/2.42                   C ) ) ) ) ) ) ))).
% 2.23/2.42  thf(zf_stmt_0, negated_conjecture,
% 2.23/2.42    (~( ![A:$i]:
% 2.23/2.42        ( ( l1_struct_0 @ A ) =>
% 2.23/2.42          ( ![B:$i]:
% 2.23/2.42            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.23/2.42              ( ![C:$i]:
% 2.23/2.42                ( ( ( v1_funct_1 @ C ) & 
% 2.23/2.42                    ( v1_funct_2 @
% 2.23/2.42                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.23/2.42                    ( m1_subset_1 @
% 2.23/2.42                      C @ 
% 2.23/2.42                      ( k1_zfmisc_1 @
% 2.23/2.42                        ( k2_zfmisc_1 @
% 2.23/2.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.23/2.42                  ( ( ( ( k2_relset_1 @
% 2.23/2.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.23/2.42                        ( k2_struct_0 @ B ) ) & 
% 2.23/2.42                      ( v2_funct_1 @ C ) ) =>
% 2.23/2.42                    ( r2_funct_2 @
% 2.23/2.42                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 2.23/2.42                      ( k2_tops_2 @
% 2.23/2.42                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.23/2.42                        ( k2_tops_2 @
% 2.23/2.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 2.23/2.42                      C ) ) ) ) ) ) ) )),
% 2.23/2.42    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 2.23/2.42  thf('3', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 2.23/2.42          sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('4', plain,
% 2.23/2.42      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.23/2.42           sk_C)
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup-', [status(thm)], ['2', '3'])).
% 2.23/2.42  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('6', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.23/2.42          sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['4', '5'])).
% 2.23/2.42  thf('7', plain,
% 2.23/2.42      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.23/2.42           sk_C)
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup-', [status(thm)], ['1', '6'])).
% 2.23/2.42  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('9', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.23/2.42          sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['7', '8'])).
% 2.23/2.42  thf('10', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('11', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('12', plain,
% 2.23/2.42      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['10', '11'])).
% 2.23/2.42  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('14', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.23/2.42      inference('demod', [status(thm)], ['12', '13'])).
% 2.23/2.42  thf(d1_funct_2, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.23/2.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.23/2.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.23/2.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.23/2.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.23/2.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.23/2.42  thf(zf_stmt_1, axiom,
% 2.23/2.42    (![C:$i,B:$i,A:$i]:
% 2.23/2.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.23/2.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.23/2.42  thf('15', plain,
% 2.23/2.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.23/2.42         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.23/2.42          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.23/2.42          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.23/2.42  thf('16', plain,
% 2.23/2.42      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 2.23/2.42        | ((k2_struct_0 @ sk_A)
% 2.23/2.42            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['14', '15'])).
% 2.23/2.42  thf('17', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('18', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('19', plain,
% 2.23/2.42      (((m1_subset_1 @ sk_C @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['17', '18'])).
% 2.23/2.42  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('21', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('demod', [status(thm)], ['19', '20'])).
% 2.23/2.42  thf(t38_relset_1, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.42       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 2.23/2.42         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.23/2.42  thf('22', plain,
% 2.23/2.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.23/2.42         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 2.23/2.42            = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.23/2.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.23/2.42      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.23/2.42  thf('23', plain,
% 2.23/2.42      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.23/2.42         (u1_struct_0 @ sk_B))
% 2.23/2.42         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['21', '22'])).
% 2.23/2.42  thf('24', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('demod', [status(thm)], ['19', '20'])).
% 2.23/2.42  thf(redefinition_k8_relset_1, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i,D:$i]:
% 2.23/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.42       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.23/2.42  thf('25', plain,
% 2.23/2.42      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.23/2.42          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 2.23/2.42      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.23/2.42  thf('26', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.23/2.42           X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.23/2.42      inference('sup-', [status(thm)], ['24', '25'])).
% 2.23/2.42  thf('27', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 2.23/2.42         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['23', '26'])).
% 2.23/2.42  thf('28', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('29', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('30', plain,
% 2.23/2.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.23/2.42         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 2.23/2.42            = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.23/2.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.23/2.42      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.23/2.42  thf('31', plain,
% 2.23/2.42      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.23/2.42         (u1_struct_0 @ sk_B))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['29', '30'])).
% 2.23/2.42  thf('32', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('33', plain,
% 2.23/2.42      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.23/2.42          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 2.23/2.42      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.23/2.42  thf('34', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.23/2.42           X0) = (k10_relat_1 @ sk_C @ X0))),
% 2.23/2.42      inference('sup-', [status(thm)], ['32', '33'])).
% 2.23/2.42  thf('35', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['31', '34'])).
% 2.23/2.42  thf('36', plain,
% 2.23/2.42      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 2.23/2.42          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['28', '35'])).
% 2.23/2.42  thf('37', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(redefinition_k2_relset_1, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.42       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.23/2.42  thf('38', plain,
% 2.23/2.42      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.23/2.42         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 2.23/2.42          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.23/2.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.23/2.42  thf('39', plain,
% 2.23/2.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42         = (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['37', '38'])).
% 2.23/2.42  thf('40', plain,
% 2.23/2.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42         = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('41', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('43', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['36', '41', '42'])).
% 2.23/2.42  thf('44', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('45', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('46', plain,
% 2.23/2.42      (((m1_subset_1 @ sk_C @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['44', '45'])).
% 2.23/2.42  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('48', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.23/2.42      inference('demod', [status(thm)], ['46', '47'])).
% 2.23/2.42  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('50', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['48', '49'])).
% 2.23/2.42  thf('51', plain,
% 2.23/2.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.23/2.42         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 2.23/2.42            = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.23/2.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.23/2.42      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.23/2.42  thf('52', plain,
% 2.23/2.42      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 2.23/2.42         (k2_relat_1 @ sk_C))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['50', '51'])).
% 2.23/2.42  thf('53', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['48', '49'])).
% 2.23/2.42  thf('54', plain,
% 2.23/2.42      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.23/2.42          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 2.23/2.42      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.23/2.42  thf('55', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 2.23/2.42           = (k10_relat_1 @ sk_C @ X0))),
% 2.23/2.42      inference('sup-', [status(thm)], ['53', '54'])).
% 2.23/2.42  thf('56', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['52', '55'])).
% 2.23/2.42  thf('57', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 2.23/2.42         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 2.23/2.42      inference('sup+', [status(thm)], ['43', '56'])).
% 2.23/2.42  thf('58', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 2.23/2.42         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['27', '57'])).
% 2.23/2.42  thf('59', plain,
% 2.23/2.42      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 2.23/2.42        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['16', '58'])).
% 2.23/2.42  thf('60', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf(zf_stmt_2, axiom,
% 2.23/2.42    (![B:$i,A:$i]:
% 2.23/2.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.23/2.42       ( zip_tseitin_0 @ B @ A ) ))).
% 2.23/2.42  thf('61', plain,
% 2.23/2.42      (![X17 : $i, X18 : $i]:
% 2.23/2.42         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.23/2.42  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.23/2.42  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.23/2.42      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.23/2.42  thf('63', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.23/2.42      inference('sup+', [status(thm)], ['61', '62'])).
% 2.23/2.42  thf('64', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('65', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.23/2.42  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.23/2.42  thf(zf_stmt_5, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.23/2.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.23/2.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.23/2.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.23/2.42  thf('66', plain,
% 2.23/2.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.23/2.42         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.23/2.42          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.23/2.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.23/2.42  thf('67', plain,
% 2.23/2.42      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['65', '66'])).
% 2.23/2.42  thf('68', plain,
% 2.23/2.42      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B)
% 2.23/2.42        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['64', '67'])).
% 2.23/2.42  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('71', plain,
% 2.23/2.42      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('demod', [status(thm)], ['68', '69', '70'])).
% 2.23/2.42  thf('72', plain,
% 2.23/2.42      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.23/2.42        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['63', '71'])).
% 2.23/2.42  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf(fc5_struct_0, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.23/2.42       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 2.23/2.42  thf('74', plain,
% 2.23/2.42      (![X34 : $i]:
% 2.23/2.42         (~ (v1_xboole_0 @ (k2_struct_0 @ X34))
% 2.23/2.42          | ~ (l1_struct_0 @ X34)
% 2.23/2.42          | (v2_struct_0 @ X34))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc5_struct_0])).
% 2.23/2.42  thf('75', plain,
% 2.23/2.42      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.23/2.42        | (v2_struct_0 @ sk_B)
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup-', [status(thm)], ['73', '74'])).
% 2.23/2.42  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('77', plain,
% 2.23/2.42      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 2.23/2.42      inference('demod', [status(thm)], ['75', '76'])).
% 2.23/2.42  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('79', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('clc', [status(thm)], ['77', '78'])).
% 2.23/2.42  thf('80', plain,
% 2.23/2.42      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['72', '79'])).
% 2.23/2.42  thf('81', plain,
% 2.23/2.42      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['60', '80'])).
% 2.23/2.42  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('83', plain,
% 2.23/2.42      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['81', '82'])).
% 2.23/2.42  thf('84', plain,
% 2.23/2.42      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 2.23/2.42      inference('demod', [status(thm)], ['59', '83'])).
% 2.23/2.42  thf('85', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('86', plain,
% 2.23/2.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.23/2.42         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.23/2.42          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.23/2.42          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.23/2.42  thf('87', plain,
% 2.23/2.42      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ((u1_struct_0 @ sk_A)
% 2.23/2.42            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['85', '86'])).
% 2.23/2.42  thf('88', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['31', '34'])).
% 2.23/2.42  thf('89', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 2.23/2.42         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 2.23/2.42      inference('sup+', [status(thm)], ['43', '56'])).
% 2.23/2.42  thf('90', plain,
% 2.23/2.42      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 2.23/2.42         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['88', '89'])).
% 2.23/2.42  thf('91', plain,
% 2.23/2.42      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['87', '90'])).
% 2.23/2.42  thf('92', plain,
% 2.23/2.42      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['72', '79'])).
% 2.23/2.42  thf('93', plain,
% 2.23/2.42      (((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 2.23/2.42      inference('demod', [status(thm)], ['91', '92'])).
% 2.23/2.42  thf('94', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['84', '93'])).
% 2.23/2.42  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('96', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['84', '93'])).
% 2.23/2.42  thf('97', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['84', '93'])).
% 2.23/2.42  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('99', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 2.23/2.42          sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['9', '94', '95', '96', '97', '98'])).
% 2.23/2.42  thf('100', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('101', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('demod', [status(thm)], ['19', '20'])).
% 2.23/2.42  thf('102', plain,
% 2.23/2.42      (((m1_subset_1 @ sk_C @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['100', '101'])).
% 2.23/2.42  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('104', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.23/2.42      inference('demod', [status(thm)], ['102', '103'])).
% 2.23/2.42  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('106', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['104', '105'])).
% 2.23/2.42  thf(d4_tops_2, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.42       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.23/2.42         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.23/2.42  thf('107', plain,
% 2.23/2.42      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.23/2.42         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 2.23/2.42          | ~ (v2_funct_1 @ X37)
% 2.23/2.42          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 2.23/2.42          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 2.23/2.42          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 2.23/2.42          | ~ (v1_funct_1 @ X37))),
% 2.23/2.42      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.23/2.42  thf('108', plain,
% 2.23/2.42      ((~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.23/2.42        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42            = (k2_funct_1 @ sk_C))
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.42        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42            != (k2_relat_1 @ sk_C)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['106', '107'])).
% 2.23/2.42  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('110', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('111', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.23/2.42      inference('demod', [status(thm)], ['12', '13'])).
% 2.23/2.42  thf('112', plain,
% 2.23/2.42      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['110', '111'])).
% 2.23/2.42  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('114', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('demod', [status(thm)], ['112', '113'])).
% 2.23/2.42  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('116', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['114', '115'])).
% 2.23/2.42  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('118', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('119', plain,
% 2.23/2.42      (![X33 : $i]:
% 2.23/2.42         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 2.23/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.23/2.42  thf('120', plain,
% 2.23/2.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42         = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('121', plain,
% 2.23/2.42      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42          = (k2_struct_0 @ sk_B))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup+', [status(thm)], ['119', '120'])).
% 2.23/2.42  thf('122', plain, ((l1_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('123', plain,
% 2.23/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42         = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('demod', [status(thm)], ['121', '122'])).
% 2.23/2.42  thf('124', plain,
% 2.23/2.42      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42          = (k2_struct_0 @ sk_B))
% 2.23/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['118', '123'])).
% 2.23/2.42  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('126', plain,
% 2.23/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.23/2.42         = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('demod', [status(thm)], ['124', '125'])).
% 2.23/2.42  thf('127', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('128', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.23/2.42      inference('sup+', [status(thm)], ['39', '40'])).
% 2.23/2.42  thf('129', plain,
% 2.23/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42         = (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['126', '127', '128'])).
% 2.23/2.42  thf('130', plain,
% 2.23/2.42      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42          = (k2_funct_1 @ sk_C))
% 2.23/2.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.23/2.42      inference('demod', [status(thm)], ['108', '109', '116', '117', '129'])).
% 2.23/2.42  thf('131', plain,
% 2.23/2.42      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42         = (k2_funct_1 @ sk_C))),
% 2.23/2.42      inference('simplify', [status(thm)], ['130'])).
% 2.23/2.42  thf('132', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.42          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42          sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['99', '131'])).
% 2.23/2.42  thf(fc6_funct_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 2.23/2.42       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.23/2.42         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 2.23/2.42         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.23/2.42  thf('133', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf('134', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf(t55_funct_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.42       ( ( v2_funct_1 @ A ) =>
% 2.23/2.42         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.23/2.42           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.23/2.42  thf('135', plain,
% 2.23/2.42      (![X5 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X5)
% 2.23/2.42          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.42          | ~ (v1_funct_1 @ X5)
% 2.23/2.42          | ~ (v1_relat_1 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.42  thf('136', plain,
% 2.23/2.42      (![X6 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X6)
% 2.23/2.42          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 2.23/2.42          | ~ (v1_funct_1 @ X6)
% 2.23/2.42          | ~ (v1_relat_1 @ X6))),
% 2.23/2.42      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.23/2.42  thf('137', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf('138', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['104', '105'])).
% 2.23/2.42  thf(t31_funct_2, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.42       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.23/2.42         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.23/2.42           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.23/2.42           ( m1_subset_1 @
% 2.23/2.42             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.23/2.42  thf('139', plain,
% 2.23/2.42      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X29)
% 2.23/2.42          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 2.23/2.42          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 2.23/2.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.23/2.42          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.23/2.42          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 2.23/2.42          | ~ (v1_funct_1 @ X29))),
% 2.23/2.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.23/2.42  thf('140', plain,
% 2.23/2.42      ((~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.23/2.42        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 2.23/2.42        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42            != (k2_relat_1 @ sk_C))
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['138', '139'])).
% 2.23/2.42  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('142', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['114', '115'])).
% 2.23/2.42  thf('143', plain,
% 2.23/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42         = (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['126', '127', '128'])).
% 2.23/2.42  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('145', plain,
% 2.23/2.42      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 2.23/2.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.23/2.42      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 2.23/2.42  thf('146', plain,
% 2.23/2.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 2.23/2.42      inference('simplify', [status(thm)], ['145'])).
% 2.23/2.42  thf(cc2_relat_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ A ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.23/2.42  thf('147', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.23/2.42          | (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X1))),
% 2.23/2.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.23/2.42  thf('148', plain,
% 2.23/2.42      ((~ (v1_relat_1 @ 
% 2.23/2.42           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))
% 2.23/2.42        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['146', '147'])).
% 2.23/2.42  thf(fc6_relat_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.23/2.42  thf('149', plain,
% 2.23/2.42      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.23/2.42  thf('150', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['148', '149'])).
% 2.23/2.42  thf('151', plain,
% 2.23/2.42      (![X6 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X6)
% 2.23/2.42          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 2.23/2.42          | ~ (v1_funct_1 @ X6)
% 2.23/2.42          | ~ (v1_relat_1 @ X6))),
% 2.23/2.42      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.23/2.42  thf('152', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf('153', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf('154', plain,
% 2.23/2.42      (![X5 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X5)
% 2.23/2.42          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.42          | ~ (v1_funct_1 @ X5)
% 2.23/2.42          | ~ (v1_relat_1 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.42  thf(t3_funct_2, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.42       ( ( v1_funct_1 @ A ) & 
% 2.23/2.42         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.23/2.42         ( m1_subset_1 @
% 2.23/2.42           A @ 
% 2.23/2.42           ( k1_zfmisc_1 @
% 2.23/2.42             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.23/2.42  thf('155', plain,
% 2.23/2.42      (![X32 : $i]:
% 2.23/2.42         ((m1_subset_1 @ X32 @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 2.23/2.42          | ~ (v1_funct_1 @ X32)
% 2.23/2.42          | ~ (v1_relat_1 @ X32))),
% 2.23/2.42      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.23/2.42  thf('156', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.23/2.42      inference('sup+', [status(thm)], ['154', '155'])).
% 2.23/2.42  thf('157', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.23/2.42               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['153', '156'])).
% 2.23/2.42  thf('158', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0))),
% 2.23/2.42      inference('simplify', [status(thm)], ['157'])).
% 2.23/2.42  thf('159', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.23/2.42               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['152', '158'])).
% 2.23/2.42  thf('160', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0))),
% 2.23/2.42      inference('simplify', [status(thm)], ['159'])).
% 2.23/2.42  thf('161', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 2.23/2.42      inference('sup+', [status(thm)], ['151', '160'])).
% 2.23/2.42  thf('162', plain,
% 2.23/2.42      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.42        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.42        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42             (k2_relat_1 @ sk_C)))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['150', '161'])).
% 2.23/2.42  thf('163', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.42      inference('demod', [status(thm)], ['104', '105'])).
% 2.23/2.42  thf('164', plain,
% 2.23/2.42      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X29)
% 2.23/2.42          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 2.23/2.42          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 2.23/2.42          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.23/2.42          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 2.23/2.42          | ~ (v1_funct_1 @ X29))),
% 2.23/2.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.23/2.42  thf('165', plain,
% 2.23/2.42      ((~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.23/2.42        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.42        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42            != (k2_relat_1 @ sk_C))
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['163', '164'])).
% 2.23/2.42  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('167', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['114', '115'])).
% 2.23/2.42  thf('168', plain,
% 2.23/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.42         = (k2_relat_1 @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['126', '127', '128'])).
% 2.23/2.42  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('170', plain,
% 2.23/2.42      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.23/2.42      inference('demod', [status(thm)], ['165', '166', '167', '168', '169'])).
% 2.23/2.42  thf('171', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.42      inference('simplify', [status(thm)], ['170'])).
% 2.23/2.42  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('174', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('175', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.23/2.42          | (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X1))),
% 2.23/2.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.23/2.42  thf('176', plain,
% 2.23/2.42      ((~ (v1_relat_1 @ 
% 2.23/2.42           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 2.23/2.42        | (v1_relat_1 @ sk_C))),
% 2.23/2.42      inference('sup-', [status(thm)], ['174', '175'])).
% 2.23/2.42  thf('177', plain,
% 2.23/2.42      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.23/2.42  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.42  thf('179', plain,
% 2.23/2.42      (![X5 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X5)
% 2.23/2.42          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.42          | ~ (v1_funct_1 @ X5)
% 2.23/2.42          | ~ (v1_relat_1 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.42  thf('180', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.23/2.42      inference('sup+', [status(thm)], ['61', '62'])).
% 2.23/2.42  thf('181', plain,
% 2.23/2.42      (![X5 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X5)
% 2.23/2.42          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.42          | ~ (v1_funct_1 @ X5)
% 2.23/2.42          | ~ (v1_relat_1 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.42  thf('182', plain,
% 2.23/2.42      (![X5 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X5)
% 2.23/2.42          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.42          | ~ (v1_funct_1 @ X5)
% 2.23/2.42          | ~ (v1_relat_1 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.42  thf('183', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf('184', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.42      inference('simplify', [status(thm)], ['170'])).
% 2.23/2.42  thf('185', plain,
% 2.23/2.42      (![X4 : $i]:
% 2.23/2.42         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 2.23/2.42          | ~ (v2_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_funct_1 @ X4)
% 2.23/2.42          | ~ (v1_relat_1 @ X4))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.42  thf('186', plain,
% 2.23/2.42      (![X6 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X6)
% 2.23/2.42          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 2.23/2.42          | ~ (v1_funct_1 @ X6)
% 2.23/2.42          | ~ (v1_relat_1 @ X6))),
% 2.23/2.42      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.23/2.42  thf('187', plain,
% 2.23/2.42      (![X5 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X5)
% 2.23/2.42          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.42          | ~ (v1_funct_1 @ X5)
% 2.23/2.42          | ~ (v1_relat_1 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.42  thf('188', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0))),
% 2.23/2.42      inference('simplify', [status(thm)], ['159'])).
% 2.23/2.42  thf('189', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0))),
% 2.23/2.42      inference('sup+', [status(thm)], ['187', '188'])).
% 2.23/2.42  thf('190', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 2.23/2.42      inference('simplify', [status(thm)], ['189'])).
% 2.23/2.42  thf('191', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ X0 @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.42             (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 2.23/2.42      inference('sup+', [status(thm)], ['186', '190'])).
% 2.23/2.42  thf('192', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | (m1_subset_1 @ X0 @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.42               (k1_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['185', '191'])).
% 2.23/2.42  thf('193', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ X0 @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.42             (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.42          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.42          | ~ (v2_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0))),
% 2.23/2.42      inference('simplify', [status(thm)], ['192'])).
% 2.23/2.42  thf('194', plain,
% 2.23/2.42      ((~ (v1_relat_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.42        | (m1_subset_1 @ sk_C @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42             (k1_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['184', '193'])).
% 2.23/2.42  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.42  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('198', plain,
% 2.23/2.42      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.42        | (m1_subset_1 @ sk_C @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42             (k1_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.23/2.42      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 2.23/2.42  thf('199', plain,
% 2.23/2.42      ((~ (v1_relat_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.42        | (m1_subset_1 @ sk_C @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42             (k1_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['183', '198'])).
% 2.23/2.42  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.42      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.42  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('203', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.42          (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.23/2.42      inference('demod', [status(thm)], ['199', '200', '201', '202'])).
% 2.23/2.42  thf('204', plain,
% 2.23/2.42      (((m1_subset_1 @ sk_C @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 2.23/2.42           (k1_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.23/2.42        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.42      inference('sup+', [status(thm)], ['182', '203'])).
% 2.23/2.43  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('208', plain,
% 2.23/2.43      ((m1_subset_1 @ sk_C @ 
% 2.23/2.43        (k1_zfmisc_1 @ 
% 2.23/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 2.23/2.43          (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.23/2.43      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 2.23/2.43  thf('209', plain,
% 2.23/2.43      (((m1_subset_1 @ sk_C @ 
% 2.23/2.43         (k1_zfmisc_1 @ 
% 2.23/2.43          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.43      inference('sup+', [status(thm)], ['181', '208'])).
% 2.23/2.43  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('213', plain,
% 2.23/2.43      ((m1_subset_1 @ sk_C @ 
% 2.23/2.43        (k1_zfmisc_1 @ 
% 2.23/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.43      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 2.23/2.43  thf('214', plain,
% 2.23/2.43      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.23/2.43         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 2.23/2.43            = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.23/2.43          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.23/2.43      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.23/2.43  thf('215', plain,
% 2.23/2.43      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 2.23/2.43         (k2_relat_1 @ sk_C))
% 2.23/2.43         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.43      inference('sup-', [status(thm)], ['213', '214'])).
% 2.23/2.43  thf('216', plain,
% 2.23/2.43      ((m1_subset_1 @ sk_C @ 
% 2.23/2.43        (k1_zfmisc_1 @ 
% 2.23/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.43      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 2.23/2.43  thf('217', plain,
% 2.23/2.43      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.23/2.43         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.23/2.43          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 2.23/2.43      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.23/2.43  thf('218', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 2.23/2.43           = (k10_relat_1 @ sk_C @ X0))),
% 2.23/2.43      inference('sup-', [status(thm)], ['216', '217'])).
% 2.23/2.43  thf('219', plain,
% 2.23/2.43      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.23/2.43      inference('sup+', [status(thm)], ['61', '62'])).
% 2.23/2.43  thf('220', plain,
% 2.23/2.43      ((m1_subset_1 @ sk_C @ 
% 2.23/2.43        (k1_zfmisc_1 @ 
% 2.23/2.43         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.43      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 2.23/2.43  thf('221', plain,
% 2.23/2.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.23/2.43         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.23/2.43          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.23/2.43          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.23/2.43  thf('222', plain,
% 2.23/2.43      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 2.23/2.43        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['220', '221'])).
% 2.23/2.43  thf('223', plain,
% 2.23/2.43      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.23/2.43        | (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['219', '222'])).
% 2.23/2.43  thf('224', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.23/2.43      inference('clc', [status(thm)], ['77', '78'])).
% 2.23/2.43  thf('225', plain,
% 2.23/2.43      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 2.23/2.43      inference('clc', [status(thm)], ['223', '224'])).
% 2.23/2.43  thf('226', plain,
% 2.23/2.43      (![X32 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 2.23/2.43          | ~ (v1_funct_1 @ X32)
% 2.23/2.43          | ~ (v1_relat_1 @ X32))),
% 2.23/2.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.23/2.43  thf('227', plain,
% 2.23/2.43      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.23/2.43         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.23/2.43          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.23/2.43          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.23/2.43  thf('228', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.23/2.43          | ((k1_relat_1 @ X0)
% 2.23/2.43              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['226', '227'])).
% 2.23/2.43  thf('229', plain,
% 2.23/2.43      ((((k1_relat_1 @ sk_C)
% 2.23/2.43          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C))),
% 2.23/2.43      inference('sup-', [status(thm)], ['225', '228'])).
% 2.23/2.43  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('232', plain,
% 2.23/2.43      (((k1_relat_1 @ sk_C)
% 2.23/2.43         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['229', '230', '231'])).
% 2.23/2.43  thf('233', plain,
% 2.23/2.43      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['215', '218', '232'])).
% 2.23/2.43  thf('234', plain,
% 2.23/2.43      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 2.23/2.43      inference('demod', [status(thm)], ['59', '83'])).
% 2.23/2.43  thf('235', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 2.23/2.43      inference('sup+', [status(thm)], ['233', '234'])).
% 2.23/2.43  thf('236', plain,
% 2.23/2.43      (![X5 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X5)
% 2.23/2.43          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.43          | ~ (v1_funct_1 @ X5)
% 2.23/2.43          | ~ (v1_relat_1 @ X5))),
% 2.23/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.43  thf('237', plain,
% 2.23/2.43      (![X5 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X5)
% 2.23/2.43          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.43          | ~ (v1_funct_1 @ X5)
% 2.23/2.43          | ~ (v1_relat_1 @ X5))),
% 2.23/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.43  thf('238', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('239', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('240', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((m1_subset_1 @ X0 @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['192'])).
% 2.23/2.43  thf('241', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | (m1_subset_1 @ X0 @ 
% 2.23/2.43             (k1_zfmisc_1 @ 
% 2.23/2.43              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43               (k1_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['239', '240'])).
% 2.23/2.43  thf('242', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((m1_subset_1 @ X0 @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['241'])).
% 2.23/2.43  thf('243', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | (m1_subset_1 @ X0 @ 
% 2.23/2.43             (k1_zfmisc_1 @ 
% 2.23/2.43              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43               (k1_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['238', '242'])).
% 2.23/2.43  thf('244', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((m1_subset_1 @ X0 @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['243'])).
% 2.23/2.43  thf('245', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((m1_subset_1 @ X0 @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0))),
% 2.23/2.43      inference('sup+', [status(thm)], ['237', '244'])).
% 2.23/2.43  thf('246', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | (m1_subset_1 @ X0 @ 
% 2.23/2.43             (k1_zfmisc_1 @ 
% 2.23/2.43              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43               (k2_relat_1 @ X0)))))),
% 2.23/2.43      inference('simplify', [status(thm)], ['245'])).
% 2.23/2.43  thf('247', plain,
% 2.23/2.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.23/2.43         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.23/2.43          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.23/2.43          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.23/2.43  thf('248', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ 
% 2.23/2.43             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ 
% 2.23/2.43               (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['246', '247'])).
% 2.23/2.43  thf('249', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ 
% 2.23/2.43             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('sup-', [status(thm)], ['236', '248'])).
% 2.23/2.43  thf('250', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ 
% 2.23/2.43           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 2.23/2.43      inference('simplify', [status(thm)], ['249'])).
% 2.23/2.43  thf('251', plain,
% 2.23/2.43      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.43        | (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 2.23/2.43           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['235', '250'])).
% 2.23/2.43  thf('252', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('254', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('255', plain,
% 2.23/2.43      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 2.23/2.43        | (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 2.23/2.43           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 2.23/2.43  thf('256', plain,
% 2.23/2.43      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.23/2.43        | (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 2.23/2.43           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['180', '255'])).
% 2.23/2.43  thf('257', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.23/2.43      inference('clc', [status(thm)], ['77', '78'])).
% 2.23/2.43  thf('258', plain,
% 2.23/2.43      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 2.23/2.43        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('clc', [status(thm)], ['256', '257'])).
% 2.23/2.43  thf('259', plain,
% 2.23/2.43      (![X5 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X5)
% 2.23/2.43          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.43          | ~ (v1_funct_1 @ X5)
% 2.23/2.43          | ~ (v1_relat_1 @ X5))),
% 2.23/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.43  thf('260', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('261', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('262', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('263', plain,
% 2.23/2.43      (![X6 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X6)
% 2.23/2.43          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 2.23/2.43          | ~ (v1_funct_1 @ X6)
% 2.23/2.43          | ~ (v1_relat_1 @ X6))),
% 2.23/2.43      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.23/2.43  thf('264', plain,
% 2.23/2.43      (![X5 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X5)
% 2.23/2.43          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.43          | ~ (v1_funct_1 @ X5)
% 2.23/2.43          | ~ (v1_relat_1 @ X5))),
% 2.23/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.43  thf('265', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('266', plain,
% 2.23/2.43      (![X4 : $i]:
% 2.23/2.43         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 2.23/2.43          | ~ (v2_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_funct_1 @ X4)
% 2.23/2.43          | ~ (v1_relat_1 @ X4))),
% 2.23/2.43      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.23/2.43  thf('267', plain,
% 2.23/2.43      (![X5 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X5)
% 2.23/2.43          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 2.23/2.43          | ~ (v1_funct_1 @ X5)
% 2.23/2.43          | ~ (v1_relat_1 @ X5))),
% 2.23/2.43      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.23/2.43  thf('268', plain,
% 2.23/2.43      (![X32 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 2.23/2.43          | ~ (v1_funct_1 @ X32)
% 2.23/2.43          | ~ (v1_relat_1 @ X32))),
% 2.23/2.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.23/2.43  thf('269', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.23/2.43      inference('sup+', [status(thm)], ['267', '268'])).
% 2.23/2.43  thf('270', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['266', '269'])).
% 2.23/2.43  thf('271', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['270'])).
% 2.23/2.43  thf('272', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['265', '271'])).
% 2.23/2.43  thf('273', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['272'])).
% 2.23/2.43  thf('274', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.23/2.43           (k1_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0))),
% 2.23/2.43      inference('sup+', [status(thm)], ['264', '273'])).
% 2.23/2.43  thf('275', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.23/2.43             (k1_relat_1 @ X0)))),
% 2.23/2.43      inference('simplify', [status(thm)], ['274'])).
% 2.23/2.43  thf('276', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 2.23/2.43      inference('sup+', [status(thm)], ['263', '275'])).
% 2.23/2.43  thf('277', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['262', '276'])).
% 2.23/2.43  thf('278', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['277'])).
% 2.23/2.43  thf('279', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['261', '278'])).
% 2.23/2.43  thf('280', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['279'])).
% 2.23/2.43  thf('281', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['260', '280'])).
% 2.23/2.43  thf('282', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['281'])).
% 2.23/2.43  thf('283', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43           (k2_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0))),
% 2.23/2.43      inference('sup+', [status(thm)], ['259', '282'])).
% 2.23/2.43  thf('284', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43             (k2_relat_1 @ X0)))),
% 2.23/2.43      inference('simplify', [status(thm)], ['283'])).
% 2.23/2.43  thf('285', plain,
% 2.23/2.43      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.23/2.43         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.23/2.43          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.23/2.43          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.23/2.43  thf('286', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ 
% 2.23/2.43               (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.23/2.43          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.23/2.43              = (k1_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 2.23/2.43                 (k2_relat_1 @ X0) @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['284', '285'])).
% 2.23/2.43  thf('287', plain,
% 2.23/2.43      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43          = (k1_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.43             (k2_relat_1 @ sk_C) @ sk_C))
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C))),
% 2.23/2.43      inference('sup-', [status(thm)], ['258', '286'])).
% 2.23/2.43  thf('288', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('289', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('290', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('291', plain,
% 2.23/2.43      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43         = (k1_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.43            (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['287', '288', '289', '290'])).
% 2.23/2.43  thf('292', plain,
% 2.23/2.43      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.43      inference('sup+', [status(thm)], ['179', '291'])).
% 2.23/2.43  thf('293', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 2.23/2.43      inference('sup+', [status(thm)], ['233', '234'])).
% 2.23/2.43  thf('294', plain,
% 2.23/2.43      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 2.23/2.43         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['52', '55'])).
% 2.23/2.43  thf('295', plain,
% 2.23/2.43      (((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 2.23/2.43      inference('demod', [status(thm)], ['91', '92'])).
% 2.23/2.43  thf('296', plain,
% 2.23/2.43      (((u1_struct_0 @ sk_A)
% 2.23/2.43         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['294', '295'])).
% 2.23/2.43  thf('297', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.23/2.43      inference('sup+', [status(thm)], ['84', '93'])).
% 2.23/2.43  thf('298', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.23/2.43      inference('sup+', [status(thm)], ['84', '93'])).
% 2.23/2.43  thf('299', plain,
% 2.23/2.43      (((k2_struct_0 @ sk_A)
% 2.23/2.43         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['296', '297', '298'])).
% 2.23/2.43  thf('300', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('301', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('302', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('303', plain,
% 2.23/2.43      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 2.23/2.43      inference('demod', [status(thm)],
% 2.23/2.43                ['292', '293', '299', '300', '301', '302'])).
% 2.23/2.43  thf('304', plain,
% 2.23/2.43      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C)))))),
% 2.23/2.43      inference('demod', [status(thm)],
% 2.23/2.43                ['162', '171', '172', '173', '178', '303'])).
% 2.23/2.43  thf('305', plain,
% 2.23/2.43      ((~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.43        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C)))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['137', '304'])).
% 2.23/2.43  thf('306', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('307', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('308', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('309', plain,
% 2.23/2.43      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.23/2.43        (k1_zfmisc_1 @ 
% 2.23/2.43         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.23/2.43      inference('demod', [status(thm)], ['305', '306', '307', '308'])).
% 2.23/2.43  thf('310', plain,
% 2.23/2.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.23/2.43         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 2.23/2.43          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.23/2.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.23/2.43  thf('311', plain,
% 2.23/2.43      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 2.23/2.43         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.23/2.43         = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['309', '310'])).
% 2.23/2.43  thf('312', plain,
% 2.23/2.43      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.43          = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.43      inference('sup+', [status(thm)], ['136', '311'])).
% 2.23/2.43  thf('313', plain,
% 2.23/2.43      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.23/2.43         = (k2_relat_1 @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['126', '127', '128'])).
% 2.23/2.43  thf('314', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('316', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('317', plain,
% 2.23/2.43      (((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('demod', [status(thm)], ['312', '313', '314', '315', '316'])).
% 2.23/2.43  thf('318', plain,
% 2.23/2.43      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.23/2.43        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('sup+', [status(thm)], ['135', '317'])).
% 2.23/2.43  thf('319', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['148', '149'])).
% 2.23/2.43  thf('320', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.43      inference('simplify', [status(thm)], ['170'])).
% 2.23/2.43  thf('321', plain,
% 2.23/2.43      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.23/2.43        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('demod', [status(thm)], ['318', '319', '320'])).
% 2.23/2.43  thf('322', plain,
% 2.23/2.43      ((~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.43        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['134', '321'])).
% 2.23/2.43  thf('323', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('324', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('325', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('326', plain,
% 2.23/2.43      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('demod', [status(thm)], ['322', '323', '324', '325'])).
% 2.23/2.43  thf('327', plain,
% 2.23/2.43      (![X32 : $i]:
% 2.23/2.43         ((m1_subset_1 @ X32 @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 2.23/2.43          | ~ (v1_funct_1 @ X32)
% 2.23/2.43          | ~ (v1_relat_1 @ X32))),
% 2.23/2.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.23/2.43  thf('328', plain,
% 2.23/2.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.23/2.43         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 2.23/2.43          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.23/2.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.23/2.43  thf('329', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_relat_1 @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['327', '328'])).
% 2.23/2.43  thf('330', plain,
% 2.23/2.43      (![X32 : $i]:
% 2.23/2.43         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 2.23/2.43          | ~ (v1_funct_1 @ X32)
% 2.23/2.43          | ~ (v1_relat_1 @ X32))),
% 2.23/2.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.23/2.43  thf('331', plain,
% 2.23/2.43      (![X32 : $i]:
% 2.23/2.43         ((m1_subset_1 @ X32 @ 
% 2.23/2.43           (k1_zfmisc_1 @ 
% 2.23/2.43            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 2.23/2.43          | ~ (v1_funct_1 @ X32)
% 2.23/2.43          | ~ (v1_relat_1 @ X32))),
% 2.23/2.43      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.23/2.43  thf('332', plain,
% 2.23/2.43      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.23/2.43         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 2.23/2.43          | ~ (v2_funct_1 @ X37)
% 2.23/2.43          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 2.23/2.43          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 2.23/2.43          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 2.23/2.43          | ~ (v1_funct_1 @ X37))),
% 2.23/2.43      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.23/2.43  thf('333', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.23/2.43          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              != (k2_relat_1 @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['331', '332'])).
% 2.23/2.43  thf('334', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43            != (k2_relat_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['333'])).
% 2.23/2.43  thf('335', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              != (k2_relat_1 @ X0)))),
% 2.23/2.43      inference('sup-', [status(thm)], ['330', '334'])).
% 2.23/2.43  thf('336', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43            != (k2_relat_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0)
% 2.23/2.43          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['335'])).
% 2.23/2.43  thf('337', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0)
% 2.23/2.43          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v2_funct_1 @ X0))),
% 2.23/2.43      inference('sup-', [status(thm)], ['329', '336'])).
% 2.23/2.43  thf('338', plain,
% 2.23/2.43      (![X0 : $i]:
% 2.23/2.43         (~ (v2_funct_1 @ X0)
% 2.23/2.43          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 2.23/2.43              = (k2_funct_1 @ X0))
% 2.23/2.43          | ~ (v1_relat_1 @ X0)
% 2.23/2.43          | ~ (v1_funct_1 @ X0))),
% 2.23/2.43      inference('simplify', [status(thm)], ['337'])).
% 2.23/2.43  thf('339', plain,
% 2.23/2.43      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ 
% 2.23/2.43          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 2.23/2.43          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.23/2.43        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.23/2.43        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('sup+', [status(thm)], ['326', '338'])).
% 2.23/2.43  thf('340', plain,
% 2.23/2.43      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 2.23/2.43      inference('demod', [status(thm)],
% 2.23/2.43                ['292', '293', '299', '300', '301', '302'])).
% 2.23/2.43  thf('341', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.43      inference('simplify', [status(thm)], ['170'])).
% 2.23/2.43  thf('342', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.23/2.43      inference('demod', [status(thm)], ['148', '149'])).
% 2.23/2.43  thf('343', plain,
% 2.23/2.43      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.23/2.43          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.23/2.43        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('demod', [status(thm)], ['339', '340', '341', '342'])).
% 2.23/2.43  thf('344', plain,
% 2.23/2.43      ((~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C)
% 2.23/2.43        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.23/2.43            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.23/2.43      inference('sup-', [status(thm)], ['133', '343'])).
% 2.23/2.43  thf('345', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('346', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('347', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('348', plain,
% 2.23/2.43      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.23/2.43         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.23/2.43      inference('demod', [status(thm)], ['344', '345', '346', '347'])).
% 2.23/2.43  thf('349', plain,
% 2.23/2.43      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.23/2.43          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['132', '348'])).
% 2.23/2.43  thf('350', plain,
% 2.23/2.43      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.23/2.43           sk_C)
% 2.23/2.43        | ~ (v1_relat_1 @ sk_C)
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | ~ (v2_funct_1 @ sk_C))),
% 2.23/2.43      inference('sup-', [status(thm)], ['0', '349'])).
% 2.23/2.43  thf('351', plain,
% 2.23/2.43      ((m1_subset_1 @ sk_C @ 
% 2.23/2.43        (k1_zfmisc_1 @ 
% 2.23/2.43         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.23/2.43      inference('demod', [status(thm)], ['19', '20'])).
% 2.23/2.43  thf(redefinition_r2_funct_2, axiom,
% 2.23/2.43    (![A:$i,B:$i,C:$i,D:$i]:
% 2.23/2.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.23/2.43         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.23/2.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.43       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.23/2.43  thf('352', plain,
% 2.23/2.43      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.23/2.43         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.23/2.43          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 2.23/2.43          | ~ (v1_funct_1 @ X25)
% 2.23/2.43          | ~ (v1_funct_1 @ X28)
% 2.23/2.43          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 2.23/2.43          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.23/2.43          | (r2_funct_2 @ X26 @ X27 @ X25 @ X28)
% 2.23/2.43          | ((X25) != (X28)))),
% 2.23/2.43      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.23/2.43  thf('353', plain,
% 2.23/2.43      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.23/2.43         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 2.23/2.43          | ~ (v1_funct_1 @ X28)
% 2.23/2.43          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 2.23/2.43          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.23/2.43      inference('simplify', [status(thm)], ['352'])).
% 2.23/2.43  thf('354', plain,
% 2.23/2.43      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.23/2.43        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.43        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.23/2.43           sk_C))),
% 2.23/2.43      inference('sup-', [status(thm)], ['351', '353'])).
% 2.23/2.43  thf('355', plain,
% 2.23/2.43      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.23/2.43      inference('demod', [status(thm)], ['12', '13'])).
% 2.23/2.43  thf('356', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('357', plain,
% 2.23/2.43      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['354', '355', '356'])).
% 2.23/2.43  thf('358', plain, ((v1_relat_1 @ sk_C)),
% 2.23/2.43      inference('demod', [status(thm)], ['176', '177'])).
% 2.23/2.43  thf('359', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('360', plain, ((v2_funct_1 @ sk_C)),
% 2.23/2.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.43  thf('361', plain, ($false),
% 2.23/2.43      inference('demod', [status(thm)], ['350', '357', '358', '359', '360'])).
% 2.23/2.43  
% 2.23/2.43  % SZS output end Refutation
% 2.23/2.43  
% 2.23/2.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
