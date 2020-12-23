%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0rvEFRXwvH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:11 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  451 (10467 expanded)
%              Number of leaves         :   49 (3058 expanded)
%              Depth                    :   42
%              Number of atoms          : 4645 (235055 expanded)
%              Number of equality atoms :  193 (6991 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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

thf('10',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k8_relset_1 @ X13 @ X14 @ X15 @ X14 )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k8_relset_1 @ X13 @ X14 @ X15 @ X14 )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('31',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k8_relset_1 @ X13 @ X14 @ X15 @ X14 )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('52',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
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
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
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
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('97',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','94','95','96'])).

thf('98',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

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

thf('105',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('110',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['116','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107','114','115','127'])).

thf('129',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['97','129'])).

thf('131',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('133',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('137',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

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

thf('140',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('148',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('149',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('153',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['151','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','159'])).

thf('161',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['149','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('163',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('167',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('178',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('180',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('181',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('182',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['181','185'])).

thf('187',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['180','186'])).

thf('188',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('192',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['187','188','189','190','191'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['179','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('204',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['177','204'])).

thf('206',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('207',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('212',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('213',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('216',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('217',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['215','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['214','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['213','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['212','224'])).

thf('226',plain,(
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
    inference('sup-',[status(thm)],['211','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
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
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['210','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['209','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['207','235'])).

thf('237',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('240',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['176','240'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('243',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('244',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('245',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('246',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['246','247','248','249'])).

thf('251',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['243','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('257',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','257'])).

thf('259',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('260',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('262',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['260','263'])).

thf('265',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('267',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('268',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('269',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['241','267','268','269','270'])).

thf('272',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['161','170','171','172','175','271'])).

thf('273',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['138','272'])).

thf('274',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('275',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['273','274','275','276'])).

thf('278',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('279',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_funct_2 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('280',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_funct_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ( X0 = X1 )
      | ~ ( r2_funct_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['277','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('284',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['241','267','268','269','270'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('289',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['289','290'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['288','291'])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['287','293'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['286','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['285','297'])).

thf('299',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('300',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['298','299','300','301'])).

thf('303',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('304',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('307',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('308',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('310',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('311',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('312',plain,(
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
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
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
    inference('sup-',[status(thm)],['309','312'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,(
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
    inference('sup-',[status(thm)],['308','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
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
    inference('sup-',[status(thm)],['305','316'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['304','318'])).

thf('320',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('321',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['319','320','321','322'])).

thf('324',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['303','323'])).

thf('325',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('326',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['324','325','326','327'])).

thf('329',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['328'])).

thf('330',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('331',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18
       != ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('332',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['330','331'])).

thf('333',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('334',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['332','333'])).

thf('335',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['282','283','284','302','329','335'])).

thf('337',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['137','336'])).

thf('338',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('339',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_funct_2 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('340',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['338','340'])).

thf('342',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['341','342'])).

thf('344',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['334'])).

thf('345',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['343','344'])).

thf('346',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('347',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['337','345','346','347','348'])).

thf('350',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('351',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['349','350'])).

thf('352',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('353',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('354',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['351','352','353'])).

thf('355',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','354'])).

thf('356',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('357',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('358',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['355','356','357','358'])).

thf('360',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('361',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('362',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('363',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('364',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('365',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('366',plain,(
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
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['366'])).

thf('368',plain,(
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
    inference('sup-',[status(thm)],['363','367'])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['368'])).

thf('370',plain,(
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
    inference('sup-',[status(thm)],['362','369'])).

thf('371',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['359','371'])).

thf('373',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['241','267','268','269','270'])).

thf('374',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['337','345','346','347','348'])).

thf('375',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('376',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('377',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['372','373','374','375','376'])).

thf('378',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['135','377'])).

thf('379',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('380',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['378','379','380','381'])).

thf('383',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('384',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k8_relset_1 @ X13 @ X14 @ X15 @ X14 )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('385',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['383','384'])).

thf('386',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('387',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('388',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['386','387'])).

thf('389',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('390',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['385','388','389'])).

thf('391',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','83'])).

thf('392',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['390','391'])).

thf('393',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['382','392'])).

thf('394',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('395',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['339'])).

thf('396',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('398',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['396','397','398'])).

thf('400',plain,(
    $false ),
    inference(demod,[status(thm)],['134','393','399'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0rvEFRXwvH
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 11:30:52 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.86/2.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.86/2.07  % Solved by: fo/fo7.sh
% 1.86/2.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.86/2.07  % done 1245 iterations in 1.598s
% 1.86/2.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.86/2.07  % SZS output start Refutation
% 1.86/2.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.86/2.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.86/2.07  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.86/2.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.86/2.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.86/2.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.86/2.07  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.86/2.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.86/2.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.86/2.07  thf(sk_B_type, type, sk_B: $i).
% 1.86/2.07  thf(sk_A_type, type, sk_A: $i).
% 1.86/2.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.86/2.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.86/2.07  thf(sk_C_type, type, sk_C: $i).
% 1.86/2.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.86/2.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.86/2.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.86/2.07  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.86/2.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.86/2.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.86/2.07  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.86/2.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.86/2.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.86/2.07  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.86/2.07  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.86/2.07  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.86/2.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.86/2.07  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.86/2.07  thf(d3_struct_0, axiom,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.86/2.07  thf('0', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('1', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('2', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf(t64_tops_2, conjecture,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( l1_struct_0 @ A ) =>
% 1.86/2.07       ( ![B:$i]:
% 1.86/2.07         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.86/2.07           ( ![C:$i]:
% 1.86/2.07             ( ( ( v1_funct_1 @ C ) & 
% 1.86/2.07                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.86/2.07                 ( m1_subset_1 @
% 1.86/2.07                   C @ 
% 1.86/2.07                   ( k1_zfmisc_1 @
% 1.86/2.07                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.86/2.07               ( ( ( ( k2_relset_1 @
% 1.86/2.07                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.86/2.07                     ( k2_struct_0 @ B ) ) & 
% 1.86/2.07                   ( v2_funct_1 @ C ) ) =>
% 1.86/2.07                 ( r2_funct_2 @
% 1.86/2.07                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.86/2.07                   ( k2_tops_2 @
% 1.86/2.07                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.86/2.07                     ( k2_tops_2 @
% 1.86/2.07                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.86/2.07                   C ) ) ) ) ) ) ))).
% 1.86/2.07  thf(zf_stmt_0, negated_conjecture,
% 1.86/2.07    (~( ![A:$i]:
% 1.86/2.07        ( ( l1_struct_0 @ A ) =>
% 1.86/2.07          ( ![B:$i]:
% 1.86/2.07            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.86/2.07              ( ![C:$i]:
% 1.86/2.07                ( ( ( v1_funct_1 @ C ) & 
% 1.86/2.07                    ( v1_funct_2 @
% 1.86/2.07                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.86/2.07                    ( m1_subset_1 @
% 1.86/2.07                      C @ 
% 1.86/2.07                      ( k1_zfmisc_1 @
% 1.86/2.07                        ( k2_zfmisc_1 @
% 1.86/2.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.86/2.07                  ( ( ( ( k2_relset_1 @
% 1.86/2.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.86/2.07                        ( k2_struct_0 @ B ) ) & 
% 1.86/2.07                      ( v2_funct_1 @ C ) ) =>
% 1.86/2.07                    ( r2_funct_2 @
% 1.86/2.07                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.86/2.07                      ( k2_tops_2 @
% 1.86/2.07                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.86/2.07                        ( k2_tops_2 @
% 1.86/2.07                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.86/2.07                      C ) ) ) ) ) ) ) )),
% 1.86/2.07    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 1.86/2.07  thf('3', plain,
% 1.86/2.07      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.86/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.86/2.07          sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('4', plain,
% 1.86/2.07      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.86/2.07            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.86/2.07           sk_C)
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup-', [status(thm)], ['2', '3'])).
% 1.86/2.07  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('6', plain,
% 1.86/2.07      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.86/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.86/2.07          sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['4', '5'])).
% 1.86/2.07  thf('7', plain,
% 1.86/2.07      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.86/2.07           sk_C)
% 1.86/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup-', [status(thm)], ['1', '6'])).
% 1.86/2.07  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('9', plain,
% 1.86/2.07      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.86/2.07          sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['7', '8'])).
% 1.86/2.07  thf('10', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('11', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('12', plain,
% 1.86/2.07      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup+', [status(thm)], ['10', '11'])).
% 1.86/2.07  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('14', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['12', '13'])).
% 1.86/2.07  thf(d1_funct_2, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.86/2.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.86/2.07           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.86/2.07             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.86/2.07         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.86/2.07           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.86/2.07             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.86/2.07  thf(zf_stmt_1, axiom,
% 1.86/2.07    (![C:$i,B:$i,A:$i]:
% 1.86/2.07     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.86/2.07       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.86/2.07  thf('15', plain,
% 1.86/2.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.86/2.07         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.86/2.07          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.86/2.07          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.86/2.07  thf('16', plain,
% 1.86/2.07      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 1.86/2.07        | ((k2_struct_0 @ sk_A)
% 1.86/2.07            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['14', '15'])).
% 1.86/2.07  thf('17', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('18', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('19', plain,
% 1.86/2.07      (((m1_subset_1 @ sk_C @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup+', [status(thm)], ['17', '18'])).
% 1.86/2.07  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('21', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('demod', [status(thm)], ['19', '20'])).
% 1.86/2.07  thf(t38_relset_1, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.86/2.07       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.86/2.07         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.86/2.07  thf('22', plain,
% 1.86/2.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.86/2.07         (((k8_relset_1 @ X13 @ X14 @ X15 @ X14)
% 1.86/2.07            = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.86/2.07          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.86/2.07      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.86/2.07  thf('23', plain,
% 1.86/2.07      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.86/2.07         (u1_struct_0 @ sk_B))
% 1.86/2.07         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['21', '22'])).
% 1.86/2.07  thf('24', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('demod', [status(thm)], ['19', '20'])).
% 1.86/2.07  thf(redefinition_k8_relset_1, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i,D:$i]:
% 1.86/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.86/2.07       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.86/2.07  thf('25', plain,
% 1.86/2.07      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.86/2.07         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.86/2.07          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.86/2.07  thf('26', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.86/2.07           X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.86/2.07      inference('sup-', [status(thm)], ['24', '25'])).
% 1.86/2.07  thf('27', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.86/2.07         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['23', '26'])).
% 1.86/2.07  thf('28', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('29', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('30', plain,
% 1.86/2.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.86/2.07         (((k8_relset_1 @ X13 @ X14 @ X15 @ X14)
% 1.86/2.07            = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.86/2.07          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.86/2.07      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.86/2.07  thf('31', plain,
% 1.86/2.07      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.86/2.07         (u1_struct_0 @ sk_B))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['29', '30'])).
% 1.86/2.07  thf('32', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('33', plain,
% 1.86/2.07      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.86/2.07         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.86/2.07          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.86/2.07  thf('34', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.86/2.07           X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.86/2.07      inference('sup-', [status(thm)], ['32', '33'])).
% 1.86/2.07  thf('35', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['31', '34'])).
% 1.86/2.07  thf('36', plain,
% 1.86/2.07      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.86/2.07          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['28', '35'])).
% 1.86/2.07  thf('37', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf(redefinition_k2_relset_1, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.86/2.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.86/2.07  thf('38', plain,
% 1.86/2.07      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.86/2.07         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 1.86/2.07          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.86/2.07  thf('39', plain,
% 1.86/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07         = (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['37', '38'])).
% 1.86/2.07  thf('40', plain,
% 1.86/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07         = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('41', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('43', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['36', '41', '42'])).
% 1.86/2.07  thf('44', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('45', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('46', plain,
% 1.86/2.07      (((m1_subset_1 @ sk_C @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['44', '45'])).
% 1.86/2.07  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('48', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.86/2.07      inference('demod', [status(thm)], ['46', '47'])).
% 1.86/2.07  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('50', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['48', '49'])).
% 1.86/2.07  thf('51', plain,
% 1.86/2.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.86/2.07         (((k8_relset_1 @ X13 @ X14 @ X15 @ X14)
% 1.86/2.07            = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.86/2.07          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.86/2.07      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.86/2.07  thf('52', plain,
% 1.86/2.07      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 1.86/2.07         (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['50', '51'])).
% 1.86/2.07  thf('53', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['48', '49'])).
% 1.86/2.07  thf('54', plain,
% 1.86/2.07      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.86/2.07         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.86/2.07          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.86/2.07  thf('55', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 1.86/2.07           = (k10_relat_1 @ sk_C @ X0))),
% 1.86/2.07      inference('sup-', [status(thm)], ['53', '54'])).
% 1.86/2.07  thf('56', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['52', '55'])).
% 1.86/2.07  thf('57', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['43', '56'])).
% 1.86/2.07  thf('58', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['27', '57'])).
% 1.86/2.07  thf('59', plain,
% 1.86/2.07      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 1.86/2.07        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['16', '58'])).
% 1.86/2.07  thf('60', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf(zf_stmt_2, axiom,
% 1.86/2.07    (![B:$i,A:$i]:
% 1.86/2.07     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.86/2.07       ( zip_tseitin_0 @ B @ A ) ))).
% 1.86/2.07  thf('61', plain,
% 1.86/2.07      (![X16 : $i, X17 : $i]:
% 1.86/2.07         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.86/2.07  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.86/2.07  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.86/2.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.86/2.07  thf('63', plain,
% 1.86/2.07      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.86/2.07      inference('sup+', [status(thm)], ['61', '62'])).
% 1.86/2.07  thf('64', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('65', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.86/2.07  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.86/2.07  thf(zf_stmt_5, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.86/2.07       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.86/2.07         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.86/2.07           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.86/2.07             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.86/2.07  thf('66', plain,
% 1.86/2.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.86/2.07         (~ (zip_tseitin_0 @ X21 @ X22)
% 1.86/2.07          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 1.86/2.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.86/2.07  thf('67', plain,
% 1.86/2.07      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.86/2.07        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['65', '66'])).
% 1.86/2.07  thf('68', plain,
% 1.86/2.07      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B)
% 1.86/2.07        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['64', '67'])).
% 1.86/2.07  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('71', plain,
% 1.86/2.07      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 1.86/2.07        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.86/2.07      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.86/2.07  thf('72', plain,
% 1.86/2.07      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['63', '71'])).
% 1.86/2.07  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf(fc5_struct_0, axiom,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.86/2.07       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.86/2.07  thf('74', plain,
% 1.86/2.07      (![X33 : $i]:
% 1.86/2.07         (~ (v1_xboole_0 @ (k2_struct_0 @ X33))
% 1.86/2.07          | ~ (l1_struct_0 @ X33)
% 1.86/2.07          | (v2_struct_0 @ X33))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.86/2.07  thf('75', plain,
% 1.86/2.07      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (v2_struct_0 @ sk_B)
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup-', [status(thm)], ['73', '74'])).
% 1.86/2.07  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('77', plain,
% 1.86/2.07      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['75', '76'])).
% 1.86/2.07  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('79', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('clc', [status(thm)], ['77', '78'])).
% 1.86/2.07  thf('80', plain,
% 1.86/2.07      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.86/2.07      inference('clc', [status(thm)], ['72', '79'])).
% 1.86/2.07  thf('81', plain,
% 1.86/2.07      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup+', [status(thm)], ['60', '80'])).
% 1.86/2.07  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('83', plain,
% 1.86/2.07      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 1.86/2.07      inference('demod', [status(thm)], ['81', '82'])).
% 1.86/2.07  thf('84', plain,
% 1.86/2.07      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['59', '83'])).
% 1.86/2.07  thf('85', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('86', plain,
% 1.86/2.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.86/2.07         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.86/2.07          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.86/2.07          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.86/2.07  thf('87', plain,
% 1.86/2.07      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.86/2.07        | ((u1_struct_0 @ sk_A)
% 1.86/2.07            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['85', '86'])).
% 1.86/2.07  thf('88', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['31', '34'])).
% 1.86/2.07  thf('89', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['43', '56'])).
% 1.86/2.07  thf('90', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['88', '89'])).
% 1.86/2.07  thf('91', plain,
% 1.86/2.07      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.86/2.07        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['87', '90'])).
% 1.86/2.07  thf('92', plain,
% 1.86/2.07      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.86/2.07      inference('clc', [status(thm)], ['72', '79'])).
% 1.86/2.07  thf('93', plain,
% 1.86/2.07      (((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['91', '92'])).
% 1.86/2.07  thf('94', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup+', [status(thm)], ['84', '93'])).
% 1.86/2.07  thf('95', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup+', [status(thm)], ['84', '93'])).
% 1.86/2.07  thf('96', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('97', plain,
% 1.86/2.07      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 1.86/2.07          sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['9', '94', '95', '96'])).
% 1.86/2.07  thf('98', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('99', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('demod', [status(thm)], ['19', '20'])).
% 1.86/2.07  thf('100', plain,
% 1.86/2.07      (((m1_subset_1 @ sk_C @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['98', '99'])).
% 1.86/2.07  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('102', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.86/2.07      inference('demod', [status(thm)], ['100', '101'])).
% 1.86/2.07  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('104', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['102', '103'])).
% 1.86/2.07  thf(d4_tops_2, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.86/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.86/2.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.86/2.07         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.86/2.07  thf('105', plain,
% 1.86/2.07      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.86/2.07         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 1.86/2.07          | ~ (v2_funct_1 @ X36)
% 1.86/2.07          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 1.86/2.07          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.86/2.07          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.86/2.07          | ~ (v1_funct_1 @ X36))),
% 1.86/2.07      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.86/2.07  thf('106', plain,
% 1.86/2.07      ((~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07            = (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07            != (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['104', '105'])).
% 1.86/2.07  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('108', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('109', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['12', '13'])).
% 1.86/2.07  thf('110', plain,
% 1.86/2.07      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['108', '109'])).
% 1.86/2.07  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('112', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['110', '111'])).
% 1.86/2.07  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('114', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['112', '113'])).
% 1.86/2.07  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('116', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('117', plain,
% 1.86/2.07      (![X32 : $i]:
% 1.86/2.07         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.86/2.07      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.86/2.07  thf('118', plain,
% 1.86/2.07      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07         = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('119', plain,
% 1.86/2.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07          = (k2_struct_0 @ sk_B))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_A))),
% 1.86/2.07      inference('sup+', [status(thm)], ['117', '118'])).
% 1.86/2.07  thf('120', plain, ((l1_struct_0 @ sk_A)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('121', plain,
% 1.86/2.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07         = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['119', '120'])).
% 1.86/2.07  thf('122', plain,
% 1.86/2.07      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07          = (k2_struct_0 @ sk_B))
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['116', '121'])).
% 1.86/2.07  thf('123', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('124', plain,
% 1.86/2.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.86/2.07         = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['122', '123'])).
% 1.86/2.07  thf('125', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('126', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('127', plain,
% 1.86/2.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07         = (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.86/2.07  thf('128', plain,
% 1.86/2.07      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07          = (k2_funct_1 @ sk_C))
% 1.86/2.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['106', '107', '114', '115', '127'])).
% 1.86/2.07  thf('129', plain,
% 1.86/2.07      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07         = (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['128'])).
% 1.86/2.07  thf('130', plain,
% 1.86/2.07      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07           (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07          sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['97', '129'])).
% 1.86/2.07  thf('131', plain,
% 1.86/2.07      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07            (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07           sk_C)
% 1.86/2.07        | ~ (l1_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup-', [status(thm)], ['0', '130'])).
% 1.86/2.07  thf('132', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.86/2.07      inference('sup+', [status(thm)], ['39', '40'])).
% 1.86/2.07  thf('133', plain, ((l1_struct_0 @ sk_B)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('134', plain,
% 1.86/2.07      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.86/2.07          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07           (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07          sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.86/2.07  thf(fc6_funct_1, axiom,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.86/2.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.86/2.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.86/2.07         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.86/2.07  thf('135', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('136', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf(t65_funct_1, axiom,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.86/2.07       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.86/2.07  thf('137', plain,
% 1.86/2.07      (![X2 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X2)
% 1.86/2.07          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 1.86/2.07          | ~ (v1_funct_1 @ X2)
% 1.86/2.07          | ~ (v1_relat_1 @ X2))),
% 1.86/2.07      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.86/2.07  thf('138', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('139', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['102', '103'])).
% 1.86/2.07  thf(t31_funct_2, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.86/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.86/2.07       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.86/2.07         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.86/2.07           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.86/2.07           ( m1_subset_1 @
% 1.86/2.07             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.86/2.07  thf('140', plain,
% 1.86/2.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X28)
% 1.86/2.07          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 1.86/2.07          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 1.86/2.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.86/2.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.86/2.07          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 1.86/2.07          | ~ (v1_funct_1 @ X28))),
% 1.86/2.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.86/2.07  thf('141', plain,
% 1.86/2.07      ((~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 1.86/2.07        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07            != (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['139', '140'])).
% 1.86/2.07  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('143', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['112', '113'])).
% 1.86/2.07  thf('144', plain,
% 1.86/2.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07         = (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.86/2.07  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('146', plain,
% 1.86/2.07      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 1.86/2.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['141', '142', '143', '144', '145'])).
% 1.86/2.07  thf('147', plain,
% 1.86/2.07      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 1.86/2.07      inference('simplify', [status(thm)], ['146'])).
% 1.86/2.07  thf(cc1_relset_1, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i]:
% 1.86/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.86/2.07       ( v1_relat_1 @ C ) ))).
% 1.86/2.07  thf('148', plain,
% 1.86/2.07      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.86/2.07         ((v1_relat_1 @ X3)
% 1.86/2.07          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.86/2.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.86/2.07  thf('149', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['147', '148'])).
% 1.86/2.07  thf('150', plain,
% 1.86/2.07      (![X2 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X2)
% 1.86/2.07          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 1.86/2.07          | ~ (v1_funct_1 @ X2)
% 1.86/2.07          | ~ (v1_relat_1 @ X2))),
% 1.86/2.07      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.86/2.07  thf('151', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('152', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf(t55_funct_1, axiom,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.86/2.07       ( ( v2_funct_1 @ A ) =>
% 1.86/2.07         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.86/2.07           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.86/2.07  thf('153', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf(t3_funct_2, axiom,
% 1.86/2.07    (![A:$i]:
% 1.86/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.86/2.07       ( ( v1_funct_1 @ A ) & 
% 1.86/2.07         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.86/2.07         ( m1_subset_1 @
% 1.86/2.07           A @ 
% 1.86/2.07           ( k1_zfmisc_1 @
% 1.86/2.07             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.86/2.07  thf('154', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((m1_subset_1 @ X31 @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf('155', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['153', '154'])).
% 1.86/2.07  thf('156', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_zfmisc_1 @ 
% 1.86/2.07              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.86/2.07               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['152', '155'])).
% 1.86/2.07  thf('157', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['156'])).
% 1.86/2.07  thf('158', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_zfmisc_1 @ 
% 1.86/2.07              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.86/2.07               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['151', '157'])).
% 1.86/2.07  thf('159', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['158'])).
% 1.86/2.07  thf('160', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['150', '159'])).
% 1.86/2.07  thf('161', plain,
% 1.86/2.07      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07             (k2_relat_1 @ sk_C)))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['149', '160'])).
% 1.86/2.07  thf('162', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['102', '103'])).
% 1.86/2.07  thf('163', plain,
% 1.86/2.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X28)
% 1.86/2.07          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 1.86/2.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.86/2.07          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 1.86/2.07          | ~ (v1_funct_1 @ X28))),
% 1.86/2.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.86/2.07  thf('164', plain,
% 1.86/2.07      ((~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07            != (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['162', '163'])).
% 1.86/2.07  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('166', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['112', '113'])).
% 1.86/2.07  thf('167', plain,
% 1.86/2.07      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.86/2.07         = (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.86/2.07  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('169', plain,
% 1.86/2.07      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 1.86/2.07  thf('170', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['169'])).
% 1.86/2.07  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('173', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('174', plain,
% 1.86/2.07      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.86/2.07         ((v1_relat_1 @ X3)
% 1.86/2.07          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.86/2.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.86/2.07  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('176', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('177', plain,
% 1.86/2.07      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.86/2.07      inference('sup+', [status(thm)], ['61', '62'])).
% 1.86/2.07  thf('178', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('179', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('180', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['147', '148'])).
% 1.86/2.07  thf('181', plain,
% 1.86/2.07      (![X2 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X2)
% 1.86/2.07          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 1.86/2.07          | ~ (v1_funct_1 @ X2)
% 1.86/2.07          | ~ (v1_relat_1 @ X2))),
% 1.86/2.07      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.86/2.07  thf('182', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('183', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['158'])).
% 1.86/2.07  thf('184', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0))),
% 1.86/2.07      inference('sup+', [status(thm)], ['182', '183'])).
% 1.86/2.07  thf('185', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_zfmisc_1 @ 
% 1.86/2.07              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.86/2.07      inference('simplify', [status(thm)], ['184'])).
% 1.86/2.07  thf('186', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((m1_subset_1 @ X0 @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['181', '185'])).
% 1.86/2.07  thf('187', plain,
% 1.86/2.07      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | (m1_subset_1 @ sk_C @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['180', '186'])).
% 1.86/2.07  thf('188', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['169'])).
% 1.86/2.07  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('192', plain,
% 1.86/2.07      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | (m1_subset_1 @ sk_C @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.86/2.07      inference('demod', [status(thm)], ['187', '188', '189', '190', '191'])).
% 1.86/2.07  thf('193', plain,
% 1.86/2.07      ((~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | (m1_subset_1 @ sk_C @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['179', '192'])).
% 1.86/2.07  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('197', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07          (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.86/2.07      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 1.86/2.07  thf('198', plain,
% 1.86/2.07      (((m1_subset_1 @ sk_C @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07           (k2_relat_1 @ sk_C))))
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup+', [status(thm)], ['178', '197'])).
% 1.86/2.07  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('202', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07          (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 1.86/2.07  thf('203', plain,
% 1.86/2.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.86/2.07         (~ (zip_tseitin_0 @ X21 @ X22)
% 1.86/2.07          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 1.86/2.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.86/2.07  thf('204', plain,
% 1.86/2.07      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 1.86/2.07         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.86/2.07        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ 
% 1.86/2.07             (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['202', '203'])).
% 1.86/2.07  thf('205', plain,
% 1.86/2.07      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 1.86/2.07           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['177', '204'])).
% 1.86/2.07  thf('206', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('clc', [status(thm)], ['77', '78'])).
% 1.86/2.07  thf('207', plain,
% 1.86/2.07      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ 
% 1.86/2.07        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('clc', [status(thm)], ['205', '206'])).
% 1.86/2.07  thf('208', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('209', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('210', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('211', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('212', plain,
% 1.86/2.07      (![X2 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X2)
% 1.86/2.07          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 1.86/2.07          | ~ (v1_funct_1 @ X2)
% 1.86/2.07          | ~ (v1_relat_1 @ X2))),
% 1.86/2.07      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.86/2.07  thf('213', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('214', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('215', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('216', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('217', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf('218', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['216', '217'])).
% 1.86/2.07  thf('219', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['215', '218'])).
% 1.86/2.07  thf('220', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['219'])).
% 1.86/2.07  thf('221', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['214', '220'])).
% 1.86/2.07  thf('222', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['221'])).
% 1.86/2.07  thf('223', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.86/2.07           (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0))),
% 1.86/2.07      inference('sup+', [status(thm)], ['213', '222'])).
% 1.86/2.07  thf('224', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.86/2.07             (k1_relat_1 @ X0)))),
% 1.86/2.07      inference('simplify', [status(thm)], ['223'])).
% 1.86/2.07  thf('225', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['212', '224'])).
% 1.86/2.07  thf('226', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['211', '225'])).
% 1.86/2.07  thf('227', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['226'])).
% 1.86/2.07  thf('228', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['210', '227'])).
% 1.86/2.07  thf('229', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['228'])).
% 1.86/2.07  thf('230', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['209', '229'])).
% 1.86/2.07  thf('231', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['230'])).
% 1.86/2.07  thf('232', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0))),
% 1.86/2.07      inference('sup+', [status(thm)], ['208', '231'])).
% 1.86/2.07  thf('233', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('simplify', [status(thm)], ['232'])).
% 1.86/2.07  thf('234', plain,
% 1.86/2.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.86/2.07         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.86/2.07          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.86/2.07          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.86/2.07  thf('235', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ 
% 1.86/2.07               (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07              = (k1_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07                 (k2_relat_1 @ X0) @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['233', '234'])).
% 1.86/2.07  thf('236', plain,
% 1.86/2.07      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07          = (k1_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07             (k2_relat_1 @ sk_C) @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['207', '235'])).
% 1.86/2.07  thf('237', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('240', plain,
% 1.86/2.07      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07         = (k1_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07            (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 1.86/2.07  thf('241', plain,
% 1.86/2.07      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup+', [status(thm)], ['176', '240'])).
% 1.86/2.07  thf('242', plain,
% 1.86/2.07      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.86/2.07      inference('sup+', [status(thm)], ['61', '62'])).
% 1.86/2.07  thf('243', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('244', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('245', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07          (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.86/2.07      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 1.86/2.07  thf('246', plain,
% 1.86/2.07      (((m1_subset_1 @ sk_C @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 1.86/2.07           (k1_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup+', [status(thm)], ['244', '245'])).
% 1.86/2.07  thf('247', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('249', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('250', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 1.86/2.07          (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.86/2.07      inference('demod', [status(thm)], ['246', '247', '248', '249'])).
% 1.86/2.07  thf('251', plain,
% 1.86/2.07      (((m1_subset_1 @ sk_C @ 
% 1.86/2.07         (k1_zfmisc_1 @ 
% 1.86/2.07          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup+', [status(thm)], ['243', '250'])).
% 1.86/2.07  thf('252', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('254', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('255', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 1.86/2.07  thf('256', plain,
% 1.86/2.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.86/2.07         (~ (zip_tseitin_0 @ X21 @ X22)
% 1.86/2.07          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 1.86/2.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.86/2.07  thf('257', plain,
% 1.86/2.07      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 1.86/2.07        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['255', '256'])).
% 1.86/2.07  thf('258', plain,
% 1.86/2.07      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['242', '257'])).
% 1.86/2.07  thf('259', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('clc', [status(thm)], ['77', '78'])).
% 1.86/2.07  thf('260', plain,
% 1.86/2.07      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('clc', [status(thm)], ['258', '259'])).
% 1.86/2.07  thf('261', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf('262', plain,
% 1.86/2.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.86/2.07         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.86/2.07          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.86/2.07          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.86/2.07  thf('263', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.86/2.07          | ((k1_relat_1 @ X0)
% 1.86/2.07              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['261', '262'])).
% 1.86/2.07  thf('264', plain,
% 1.86/2.07      ((((k1_relat_1 @ sk_C)
% 1.86/2.07          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['260', '263'])).
% 1.86/2.07  thf('265', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('266', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('267', plain,
% 1.86/2.07      (((k1_relat_1 @ sk_C)
% 1.86/2.07         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['264', '265', '266'])).
% 1.86/2.07  thf('268', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('269', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('270', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('271', plain,
% 1.86/2.07      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['241', '267', '268', '269', '270'])).
% 1.86/2.07  thf('272', plain,
% 1.86/2.07      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))))),
% 1.86/2.07      inference('demod', [status(thm)],
% 1.86/2.07                ['161', '170', '171', '172', '175', '271'])).
% 1.86/2.07  thf('273', plain,
% 1.86/2.07      ((~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['138', '272'])).
% 1.86/2.07  thf('274', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('275', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('276', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('277', plain,
% 1.86/2.07      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['273', '274', '275', '276'])).
% 1.86/2.07  thf('278', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((m1_subset_1 @ X31 @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf(redefinition_r2_funct_2, axiom,
% 1.86/2.07    (![A:$i,B:$i,C:$i,D:$i]:
% 1.86/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.86/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.86/2.07         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.86/2.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.86/2.07       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.86/2.07  thf('279', plain,
% 1.86/2.07      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.86/2.07         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.86/2.07          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 1.86/2.07          | ~ (v1_funct_1 @ X24)
% 1.86/2.07          | ~ (v1_funct_1 @ X27)
% 1.86/2.07          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.86/2.07          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.86/2.07          | ((X24) = (X27))
% 1.86/2.07          | ~ (r2_funct_2 @ X25 @ X26 @ X24 @ X27))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.86/2.07  thf('280', plain,
% 1.86/2.07      (![X0 : $i, X1 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (r2_funct_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 1.86/2.07          | ((X0) = (X1))
% 1.86/2.07          | ~ (m1_subset_1 @ X1 @ 
% 1.86/2.07               (k1_zfmisc_1 @ 
% 1.86/2.07                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.86/2.07          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['278', '279'])).
% 1.86/2.07  thf('281', plain,
% 1.86/2.07      (![X0 : $i, X1 : $i]:
% 1.86/2.07         (~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (m1_subset_1 @ X1 @ 
% 1.86/2.07               (k1_zfmisc_1 @ 
% 1.86/2.07                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.86/2.07          | ((X0) = (X1))
% 1.86/2.07          | ~ (r2_funct_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['280'])).
% 1.86/2.07  thf('282', plain,
% 1.86/2.07      ((~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 1.86/2.07             (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.86/2.07        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.86/2.07        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07             (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.86/2.07        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['277', '281'])).
% 1.86/2.07  thf('283', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('284', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('285', plain,
% 1.86/2.07      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['241', '267', '268', '269', '270'])).
% 1.86/2.07  thf('286', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('287', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('288', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('289', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('290', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.86/2.07             (k1_relat_1 @ X0)))),
% 1.86/2.07      inference('simplify', [status(thm)], ['223'])).
% 1.86/2.07  thf('291', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['289', '290'])).
% 1.86/2.07  thf('292', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['288', '291'])).
% 1.86/2.07  thf('293', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['292'])).
% 1.86/2.07  thf('294', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['287', '293'])).
% 1.86/2.07  thf('295', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['294'])).
% 1.86/2.07  thf('296', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07             (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['286', '295'])).
% 1.86/2.07  thf('297', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.86/2.07           (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['296'])).
% 1.86/2.07  thf('298', plain,
% 1.86/2.07      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07         (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup+', [status(thm)], ['285', '297'])).
% 1.86/2.07  thf('299', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('300', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('301', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('302', plain,
% 1.86/2.07      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.86/2.07        (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['298', '299', '300', '301'])).
% 1.86/2.07  thf('303', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('304', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['169'])).
% 1.86/2.07  thf('305', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.86/2.07  thf('306', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_zfmisc_1 @ 
% 1.86/2.07              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.86/2.07      inference('simplify', [status(thm)], ['184'])).
% 1.86/2.07  thf('307', plain,
% 1.86/2.07      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.86/2.07         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 1.86/2.07          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.86/2.07  thf('308', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.86/2.07              (k2_funct_1 @ X0)) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['306', '307'])).
% 1.86/2.07  thf('309', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.86/2.07             (k1_relat_1 @ X0)))),
% 1.86/2.07      inference('simplify', [status(thm)], ['223'])).
% 1.86/2.07  thf('310', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.86/2.07             (k1_zfmisc_1 @ 
% 1.86/2.07              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.86/2.07      inference('simplify', [status(thm)], ['184'])).
% 1.86/2.07  thf('311', plain,
% 1.86/2.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X28)
% 1.86/2.07          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 1.86/2.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.86/2.07          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 1.86/2.07          | ~ (v1_funct_1 @ X28))),
% 1.86/2.07      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.86/2.07  thf('312', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.86/2.07               (k1_relat_1 @ X0))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.86/2.07              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['310', '311'])).
% 1.86/2.07  thf('313', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.86/2.07              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('sup-', [status(thm)], ['309', '312'])).
% 1.86/2.07  thf('314', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.86/2.07              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['313'])).
% 1.86/2.07  thf('315', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['308', '314'])).
% 1.86/2.07  thf('316', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0)))),
% 1.86/2.07      inference('simplify', [status(thm)], ['315'])).
% 1.86/2.07  thf('317', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['305', '316'])).
% 1.86/2.07  thf('318', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.86/2.07          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.86/2.07          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['317'])).
% 1.86/2.07  thf('319', plain,
% 1.86/2.07      ((~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 1.86/2.07        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['304', '318'])).
% 1.86/2.07  thf('320', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('321', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('322', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('323', plain,
% 1.86/2.07      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 1.86/2.07        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['319', '320', '321', '322'])).
% 1.86/2.07  thf('324', plain,
% 1.86/2.07      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['303', '323'])).
% 1.86/2.07  thf('325', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('326', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('327', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('328', plain,
% 1.86/2.07      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.86/2.07        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['324', '325', '326', '327'])).
% 1.86/2.07  thf('329', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('simplify', [status(thm)], ['328'])).
% 1.86/2.07  thf('330', plain,
% 1.86/2.07      (((k1_relat_1 @ sk_C)
% 1.86/2.07         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['264', '265', '266'])).
% 1.86/2.07  thf('331', plain,
% 1.86/2.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.86/2.07         (((X18) != (k1_relset_1 @ X18 @ X19 @ X20))
% 1.86/2.07          | (v1_funct_2 @ X20 @ X18 @ X19)
% 1.86/2.07          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.86/2.07  thf('332', plain,
% 1.86/2.07      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.86/2.07        | ~ (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 1.86/2.07        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['330', '331'])).
% 1.86/2.07  thf('333', plain,
% 1.86/2.07      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('clc', [status(thm)], ['258', '259'])).
% 1.86/2.07  thf('334', plain,
% 1.86/2.07      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.86/2.07        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['332', '333'])).
% 1.86/2.07  thf('335', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['334'])).
% 1.86/2.07  thf('336', plain,
% 1.86/2.07      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 1.86/2.07           (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.86/2.07        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)],
% 1.86/2.07                ['282', '283', '284', '302', '329', '335'])).
% 1.86/2.07  thf('337', plain,
% 1.86/2.07      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C)
% 1.86/2.07        | ~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.86/2.07      inference('sup-', [status(thm)], ['137', '336'])).
% 1.86/2.07  thf('338', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 1.86/2.07  thf('339', plain,
% 1.86/2.07      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.86/2.07         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.86/2.07          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 1.86/2.07          | ~ (v1_funct_1 @ X24)
% 1.86/2.07          | ~ (v1_funct_1 @ X27)
% 1.86/2.07          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.86/2.07          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.86/2.07          | (r2_funct_2 @ X25 @ X26 @ X24 @ X27)
% 1.86/2.07          | ((X24) != (X27)))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.86/2.07  thf('340', plain,
% 1.86/2.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.86/2.07         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 1.86/2.07          | ~ (v1_funct_1 @ X27)
% 1.86/2.07          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.86/2.07          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.86/2.07      inference('simplify', [status(thm)], ['339'])).
% 1.86/2.07  thf('341', plain,
% 1.86/2.07      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['338', '340'])).
% 1.86/2.07  thf('342', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('343', plain,
% 1.86/2.07      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.86/2.07        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['341', '342'])).
% 1.86/2.07  thf('344', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['334'])).
% 1.86/2.07  thf('345', plain,
% 1.86/2.07      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['343', '344'])).
% 1.86/2.07  thf('346', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('347', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('348', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('349', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['337', '345', '346', '347', '348'])).
% 1.86/2.07  thf('350', plain,
% 1.86/2.07      (![X1 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X1)
% 1.86/2.07          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.86/2.07          | ~ (v1_funct_1 @ X1)
% 1.86/2.07          | ~ (v1_relat_1 @ X1))),
% 1.86/2.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.86/2.07  thf('351', plain,
% 1.86/2.07      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['349', '350'])).
% 1.86/2.07  thf('352', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['147', '148'])).
% 1.86/2.07  thf('353', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['169'])).
% 1.86/2.07  thf('354', plain,
% 1.86/2.07      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['351', '352', '353'])).
% 1.86/2.07  thf('355', plain,
% 1.86/2.07      ((~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['136', '354'])).
% 1.86/2.07  thf('356', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('357', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('358', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('359', plain,
% 1.86/2.07      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['355', '356', '357', '358'])).
% 1.86/2.07  thf('360', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((m1_subset_1 @ X31 @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf('361', plain,
% 1.86/2.07      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.86/2.07         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 1.86/2.07          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.86/2.07  thf('362', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['360', '361'])).
% 1.86/2.07  thf('363', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf('364', plain,
% 1.86/2.07      (![X31 : $i]:
% 1.86/2.07         ((m1_subset_1 @ X31 @ 
% 1.86/2.07           (k1_zfmisc_1 @ 
% 1.86/2.07            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.86/2.07          | ~ (v1_funct_1 @ X31)
% 1.86/2.07          | ~ (v1_relat_1 @ X31))),
% 1.86/2.07      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.86/2.07  thf('365', plain,
% 1.86/2.07      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.86/2.07         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 1.86/2.07          | ~ (v2_funct_1 @ X36)
% 1.86/2.07          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 1.86/2.07          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.86/2.07          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.86/2.07          | ~ (v1_funct_1 @ X36))),
% 1.86/2.07      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.86/2.07  thf('366', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              != (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['364', '365'])).
% 1.86/2.07  thf('367', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07            != (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['366'])).
% 1.86/2.07  thf('368', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              != (k2_relat_1 @ X0)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['363', '367'])).
% 1.86/2.07  thf('369', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07            != (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['368'])).
% 1.86/2.07  thf('370', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0)
% 1.86/2.07          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v2_funct_1 @ X0))),
% 1.86/2.07      inference('sup-', [status(thm)], ['362', '369'])).
% 1.86/2.07  thf('371', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         (~ (v2_funct_1 @ X0)
% 1.86/2.07          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.86/2.07              = (k2_funct_1 @ X0))
% 1.86/2.07          | ~ (v1_relat_1 @ X0)
% 1.86/2.07          | ~ (v1_funct_1 @ X0))),
% 1.86/2.07      inference('simplify', [status(thm)], ['370'])).
% 1.86/2.07  thf('372', plain,
% 1.86/2.07      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ 
% 1.86/2.07          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.86/2.07          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.86/2.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('sup+', [status(thm)], ['359', '371'])).
% 1.86/2.07  thf('373', plain,
% 1.86/2.07      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['241', '267', '268', '269', '270'])).
% 1.86/2.07  thf('374', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['337', '345', '346', '347', '348'])).
% 1.86/2.07  thf('375', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('simplify', [status(thm)], ['169'])).
% 1.86/2.07  thf('376', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['147', '148'])).
% 1.86/2.07  thf('377', plain,
% 1.86/2.07      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.86/2.07          (k2_funct_1 @ sk_C)) = (sk_C))
% 1.86/2.07        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['372', '373', '374', '375', '376'])).
% 1.86/2.07  thf('378', plain,
% 1.86/2.07      ((~ (v1_relat_1 @ sk_C)
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | ~ (v2_funct_1 @ sk_C)
% 1.86/2.07        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.86/2.07            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.86/2.07      inference('sup-', [status(thm)], ['135', '377'])).
% 1.86/2.07  thf('379', plain, ((v1_relat_1 @ sk_C)),
% 1.86/2.07      inference('sup-', [status(thm)], ['173', '174'])).
% 1.86/2.07  thf('380', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('381', plain, ((v2_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('382', plain,
% 1.86/2.07      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.86/2.07         (k2_funct_1 @ sk_C)) = (sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['378', '379', '380', '381'])).
% 1.86/2.07  thf('383', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 1.86/2.07  thf('384', plain,
% 1.86/2.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.86/2.07         (((k8_relset_1 @ X13 @ X14 @ X15 @ X14)
% 1.86/2.07            = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.86/2.07          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.86/2.07      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.86/2.07  thf('385', plain,
% 1.86/2.07      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 1.86/2.07         (k2_relat_1 @ sk_C))
% 1.86/2.07         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['383', '384'])).
% 1.86/2.07  thf('386', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.86/2.07      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 1.86/2.07  thf('387', plain,
% 1.86/2.07      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.86/2.07         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.86/2.07          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 1.86/2.07      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.86/2.07  thf('388', plain,
% 1.86/2.07      (![X0 : $i]:
% 1.86/2.07         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 1.86/2.07           = (k10_relat_1 @ sk_C @ X0))),
% 1.86/2.07      inference('sup-', [status(thm)], ['386', '387'])).
% 1.86/2.07  thf('389', plain,
% 1.86/2.07      (((k1_relat_1 @ sk_C)
% 1.86/2.07         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['264', '265', '266'])).
% 1.86/2.07  thf('390', plain,
% 1.86/2.07      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['385', '388', '389'])).
% 1.86/2.07  thf('391', plain,
% 1.86/2.07      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 1.86/2.07      inference('demod', [status(thm)], ['59', '83'])).
% 1.86/2.07  thf('392', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.86/2.07      inference('sup+', [status(thm)], ['390', '391'])).
% 1.86/2.07  thf('393', plain,
% 1.86/2.07      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.86/2.07         (k2_funct_1 @ sk_C)) = (sk_C))),
% 1.86/2.07      inference('demod', [status(thm)], ['382', '392'])).
% 1.86/2.07  thf('394', plain,
% 1.86/2.07      ((m1_subset_1 @ sk_C @ 
% 1.86/2.07        (k1_zfmisc_1 @ 
% 1.86/2.07         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.86/2.07      inference('demod', [status(thm)], ['19', '20'])).
% 1.86/2.07  thf('395', plain,
% 1.86/2.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.86/2.07         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 1.86/2.07          | ~ (v1_funct_1 @ X27)
% 1.86/2.07          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.86/2.07          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.86/2.07      inference('simplify', [status(thm)], ['339'])).
% 1.86/2.07  thf('396', plain,
% 1.86/2.07      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.86/2.07        | ~ (v1_funct_1 @ sk_C)
% 1.86/2.07        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.86/2.07           sk_C))),
% 1.86/2.07      inference('sup-', [status(thm)], ['394', '395'])).
% 1.86/2.07  thf('397', plain,
% 1.86/2.07      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.86/2.07      inference('demod', [status(thm)], ['12', '13'])).
% 1.86/2.07  thf('398', plain, ((v1_funct_1 @ sk_C)),
% 1.86/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.86/2.07  thf('399', plain,
% 1.86/2.07      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 1.86/2.07      inference('demod', [status(thm)], ['396', '397', '398'])).
% 1.86/2.07  thf('400', plain, ($false),
% 1.86/2.07      inference('demod', [status(thm)], ['134', '393', '399'])).
% 1.86/2.07  
% 1.86/2.07  % SZS output end Refutation
% 1.86/2.07  
% 1.86/2.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
