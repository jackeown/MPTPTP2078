%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1I8RGNGo4q

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:48 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  323 (9298 expanded)
%              Number of leaves         :   47 (2661 expanded)
%              Depth                    :   35
%              Number of atoms          : 2820 (234208 expanded)
%              Number of equality atoms :  172 (11836 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','39'])).

thf('41',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('44',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','52'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X42 @ X43 @ X44 ) @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('65',plain,
    ( ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['1','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

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

thf('76',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','87','88','102'])).

thf('104',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','104','105'])).

thf('107',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('109',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

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

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('113',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('116',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','52'])).

thf('120',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X42 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','52'])).

thf('127',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('134',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['132','137'])).

thf('139',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('141',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','143'])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['118','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('147',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

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

thf('149',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('150',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('154',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['153','156'])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('160',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['160','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('168',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','39'])).

thf('170',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('175',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['171','172','175'])).

thf('177',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['171','172','175'])).

thf('178',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('179',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['168','176','177','178'])).

thf('180',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','143'])).

thf('181',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('182',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('184',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','189'])).

thf('191',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('192',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('194',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['161'])).

thf('195',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','197'])).

thf('199',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['191','200'])).

thf('202',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('203',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('204',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['171','172','175'])).

thf('206',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('207',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','207'])).

thf('209',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['161'])).

thf('211',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['209','210'])).

thf('212',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['179','211'])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','143'])).

thf('214',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('215',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('217',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','52'])).

thf('218',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X42 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('219',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('222',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['216','222'])).

thf('224',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('225',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('228',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','104','105'])).

thf('230',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['215','228','229'])).

thf('231',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('232',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','143'])).

thf('234',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('235',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','143'])).

thf('237',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('238',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('240',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('241',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('242',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('244',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('247',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X33 )
       != X32 )
      | ( v1_partfun1 @ X33 @ X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('248',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v4_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) )
      | ( v1_partfun1 @ X33 @ ( k1_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['246','248'])).

thf('250',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['245','249'])).

thf('251',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('252',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('255',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['250','251','252','253','254'])).

thf('256',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['239','255'])).

thf('257',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('261',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('262',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('264',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('265',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['232','235','238','265'])).

thf('267',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('268',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('270',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('272',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['212','272'])).

thf('274',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['158','273'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1I8RGNGo4q
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:38:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.25/2.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.25/2.50  % Solved by: fo/fo7.sh
% 2.25/2.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.50  % done 918 iterations in 2.022s
% 2.25/2.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.25/2.50  % SZS output start Refutation
% 2.25/2.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.25/2.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.25/2.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.25/2.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.25/2.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.25/2.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.25/2.50  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.25/2.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.25/2.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.25/2.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.25/2.50  thf(sk_C_type, type, sk_C: $i).
% 2.25/2.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.25/2.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.25/2.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.25/2.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.25/2.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.25/2.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.25/2.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.25/2.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.25/2.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.25/2.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.25/2.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.25/2.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.25/2.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.25/2.50  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.25/2.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.25/2.50  thf(d3_struct_0, axiom,
% 2.25/2.50    (![A:$i]:
% 2.25/2.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.25/2.50  thf('0', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('1', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('2', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf(t62_tops_2, conjecture,
% 2.25/2.50    (![A:$i]:
% 2.25/2.50     ( ( l1_struct_0 @ A ) =>
% 2.25/2.50       ( ![B:$i]:
% 2.25/2.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.25/2.50           ( ![C:$i]:
% 2.25/2.50             ( ( ( v1_funct_1 @ C ) & 
% 2.25/2.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.25/2.50                 ( m1_subset_1 @
% 2.25/2.50                   C @ 
% 2.25/2.50                   ( k1_zfmisc_1 @
% 2.25/2.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.25/2.50               ( ( ( ( k2_relset_1 @
% 2.25/2.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.25/2.50                     ( k2_struct_0 @ B ) ) & 
% 2.25/2.50                   ( v2_funct_1 @ C ) ) =>
% 2.25/2.50                 ( ( ( k1_relset_1 @
% 2.25/2.50                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.50                       ( k2_tops_2 @
% 2.25/2.50                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.25/2.50                     ( k2_struct_0 @ B ) ) & 
% 2.25/2.50                   ( ( k2_relset_1 @
% 2.25/2.50                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.50                       ( k2_tops_2 @
% 2.25/2.50                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.25/2.50                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.25/2.50  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.50    (~( ![A:$i]:
% 2.25/2.50        ( ( l1_struct_0 @ A ) =>
% 2.25/2.50          ( ![B:$i]:
% 2.25/2.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.25/2.50              ( ![C:$i]:
% 2.25/2.50                ( ( ( v1_funct_1 @ C ) & 
% 2.25/2.50                    ( v1_funct_2 @
% 2.25/2.50                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.25/2.50                    ( m1_subset_1 @
% 2.25/2.50                      C @ 
% 2.25/2.50                      ( k1_zfmisc_1 @
% 2.25/2.50                        ( k2_zfmisc_1 @
% 2.25/2.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.25/2.50                  ( ( ( ( k2_relset_1 @
% 2.25/2.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.25/2.50                        ( k2_struct_0 @ B ) ) & 
% 2.25/2.50                      ( v2_funct_1 @ C ) ) =>
% 2.25/2.50                    ( ( ( k1_relset_1 @
% 2.25/2.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.50                          ( k2_tops_2 @
% 2.25/2.50                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.25/2.50                        ( k2_struct_0 @ B ) ) & 
% 2.25/2.50                      ( ( k2_relset_1 @
% 2.25/2.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.50                          ( k2_tops_2 @
% 2.25/2.50                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.25/2.50                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.25/2.50    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 2.25/2.50  thf('3', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('4', plain,
% 2.25/2.50      (((m1_subset_1 @ sk_C @ 
% 2.25/2.50         (k1_zfmisc_1 @ 
% 2.25/2.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_A))),
% 2.25/2.50      inference('sup+', [status(thm)], ['2', '3'])).
% 2.25/2.50  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('6', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['4', '5'])).
% 2.25/2.50  thf('7', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('8', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('9', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('10', plain,
% 2.25/2.50      (((m1_subset_1 @ sk_C @ 
% 2.25/2.50         (k1_zfmisc_1 @ 
% 2.25/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['8', '9'])).
% 2.25/2.50  thf('11', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('12', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['10', '11'])).
% 2.25/2.50  thf('13', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf(redefinition_k2_relset_1, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.25/2.50  thf('14', plain,
% 2.25/2.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.25/2.50         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.25/2.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.25/2.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.25/2.50  thf('15', plain,
% 2.25/2.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['13', '14'])).
% 2.25/2.50  thf('16', plain,
% 2.25/2.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('17', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('18', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['12', '17'])).
% 2.25/2.50  thf(cc5_funct_2, axiom,
% 2.25/2.50    (![A:$i,B:$i]:
% 2.25/2.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.25/2.50       ( ![C:$i]:
% 2.25/2.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.50           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 2.25/2.50             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 2.25/2.50  thf('19', plain,
% 2.25/2.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.25/2.50         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.25/2.50          | (v1_partfun1 @ X21 @ X22)
% 2.25/2.50          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 2.25/2.50          | ~ (v1_funct_1 @ X21)
% 2.25/2.50          | (v1_xboole_0 @ X23))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc5_funct_2])).
% 2.25/2.50  thf('20', plain,
% 2.25/2.50      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['18', '19'])).
% 2.25/2.50  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('22', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('23', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('24', plain,
% 2.25/2.50      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['22', '23'])).
% 2.25/2.50  thf('25', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('26', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['24', '25'])).
% 2.25/2.50  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('28', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['26', '27'])).
% 2.25/2.50  thf('29', plain,
% 2.25/2.50      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.25/2.50      inference('demod', [status(thm)], ['20', '21', '28'])).
% 2.25/2.50  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('31', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf(fc2_struct_0, axiom,
% 2.25/2.50    (![A:$i]:
% 2.25/2.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.25/2.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.25/2.50  thf('32', plain,
% 2.25/2.50      (![X35 : $i]:
% 2.25/2.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 2.25/2.50          | ~ (l1_struct_0 @ X35)
% 2.25/2.50          | (v2_struct_0 @ X35))),
% 2.25/2.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.25/2.50  thf('33', plain,
% 2.25/2.50      (![X0 : $i]:
% 2.25/2.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.25/2.50          | ~ (l1_struct_0 @ X0)
% 2.25/2.50          | (v2_struct_0 @ X0)
% 2.25/2.50          | ~ (l1_struct_0 @ X0))),
% 2.25/2.50      inference('sup-', [status(thm)], ['31', '32'])).
% 2.25/2.50  thf('34', plain,
% 2.25/2.50      (![X0 : $i]:
% 2.25/2.50         ((v2_struct_0 @ X0)
% 2.25/2.50          | ~ (l1_struct_0 @ X0)
% 2.25/2.50          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 2.25/2.50      inference('simplify', [status(thm)], ['33'])).
% 2.25/2.50  thf('35', plain,
% 2.25/2.50      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1)
% 2.25/2.50        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup-', [status(thm)], ['30', '34'])).
% 2.25/2.50  thf('36', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('37', plain,
% 2.25/2.50      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['35', '36'])).
% 2.25/2.50  thf('38', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('clc', [status(thm)], ['37', '38'])).
% 2.25/2.50  thf('40', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.25/2.50      inference('clc', [status(thm)], ['29', '39'])).
% 2.25/2.50  thf('41', plain,
% 2.25/2.50      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.25/2.50      inference('sup+', [status(thm)], ['7', '40'])).
% 2.25/2.50  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('43', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['41', '42'])).
% 2.25/2.50  thf(d4_partfun1, axiom,
% 2.25/2.50    (![A:$i,B:$i]:
% 2.25/2.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.25/2.50       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.25/2.50  thf('44', plain,
% 2.25/2.50      (![X32 : $i, X33 : $i]:
% 2.25/2.50         (~ (v1_partfun1 @ X33 @ X32)
% 2.25/2.50          | ((k1_relat_1 @ X33) = (X32))
% 2.25/2.50          | ~ (v4_relat_1 @ X33 @ X32)
% 2.25/2.50          | ~ (v1_relat_1 @ X33))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.25/2.50  thf('45', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.50        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 2.25/2.50        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['43', '44'])).
% 2.25/2.50  thf('46', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf(cc1_relset_1, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.50       ( v1_relat_1 @ C ) ))).
% 2.25/2.50  thf('47', plain,
% 2.25/2.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.25/2.50         ((v1_relat_1 @ X12)
% 2.25/2.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.25/2.50  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('49', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['4', '5'])).
% 2.25/2.50  thf(cc2_relset_1, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.25/2.50  thf('50', plain,
% 2.25/2.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.25/2.50         ((v4_relat_1 @ X15 @ X16)
% 2.25/2.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.25/2.50  thf('51', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('sup-', [status(thm)], ['49', '50'])).
% 2.25/2.50  thf('52', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('53', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['6', '52'])).
% 2.25/2.50  thf(dt_k2_tops_2, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.50       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 2.25/2.50         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 2.25/2.50         ( m1_subset_1 @
% 2.25/2.50           ( k2_tops_2 @ A @ B @ C ) @ 
% 2.25/2.50           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 2.25/2.50  thf('54', plain,
% 2.25/2.50      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.25/2.50         ((v1_funct_2 @ (k2_tops_2 @ X42 @ X43 @ X44) @ X43 @ X42)
% 2.25/2.50          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.25/2.50          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 2.25/2.50          | ~ (v1_funct_1 @ X44))),
% 2.25/2.50      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 2.25/2.50  thf('55', plain,
% 2.25/2.50      ((~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | (v1_funct_2 @ 
% 2.25/2.50           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C) @ 
% 2.25/2.50           (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['53', '54'])).
% 2.25/2.50  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('57', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('58', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('59', plain,
% 2.25/2.50      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_A))),
% 2.25/2.50      inference('sup+', [status(thm)], ['57', '58'])).
% 2.25/2.50  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('61', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['59', '60'])).
% 2.25/2.50  thf('62', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('63', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['61', '62'])).
% 2.25/2.50  thf('64', plain,
% 2.25/2.50      ((v1_funct_2 @ 
% 2.25/2.50        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C) @ 
% 2.25/2.50        (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['55', '56', '63'])).
% 2.25/2.50  thf('65', plain,
% 2.25/2.50      (((v1_funct_2 @ 
% 2.25/2.50         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C) @ 
% 2.25/2.50         (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['1', '64'])).
% 2.25/2.50  thf('66', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('67', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('68', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['4', '5'])).
% 2.25/2.50  thf('69', plain,
% 2.25/2.50      (((m1_subset_1 @ sk_C @ 
% 2.25/2.50         (k1_zfmisc_1 @ 
% 2.25/2.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['67', '68'])).
% 2.25/2.50  thf('70', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('71', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['69', '70'])).
% 2.25/2.50  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('73', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.50  thf('74', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('75', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['73', '74'])).
% 2.25/2.50  thf(d4_tops_2, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.50       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.25/2.50         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.25/2.50  thf('76', plain,
% 2.25/2.50      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.50         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 2.25/2.50          | ~ (v2_funct_1 @ X41)
% 2.25/2.50          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 2.25/2.50          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 2.25/2.50          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 2.25/2.50          | ~ (v1_funct_1 @ X41))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.25/2.50  thf('77', plain,
% 2.25/2.50      ((~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50            = (k2_funct_1 @ sk_C))
% 2.25/2.50        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.50        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50            != (k2_relat_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['75', '76'])).
% 2.25/2.50  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('79', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('80', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['59', '60'])).
% 2.25/2.50  thf('81', plain,
% 2.25/2.50      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['79', '80'])).
% 2.25/2.50  thf('82', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('83', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['81', '82'])).
% 2.25/2.50  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('85', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['83', '84'])).
% 2.25/2.50  thf('86', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('87', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['85', '86'])).
% 2.25/2.50  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('89', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('90', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('91', plain,
% 2.25/2.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('92', plain,
% 2.25/2.50      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50          = (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_A))),
% 2.25/2.50      inference('sup+', [status(thm)], ['90', '91'])).
% 2.25/2.50  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('94', plain,
% 2.25/2.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['92', '93'])).
% 2.25/2.50  thf('95', plain,
% 2.25/2.50      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50          = (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['89', '94'])).
% 2.25/2.50  thf('96', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('97', plain,
% 2.25/2.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['95', '96'])).
% 2.25/2.50  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('100', plain,
% 2.25/2.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50         = (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['97', '98', '99'])).
% 2.25/2.50  thf('101', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('102', plain,
% 2.25/2.50      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50         = (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['100', '101'])).
% 2.25/2.50  thf('103', plain,
% 2.25/2.50      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50          = (k2_funct_1 @ sk_C))
% 2.25/2.50        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.25/2.50      inference('demod', [status(thm)], ['77', '78', '87', '88', '102'])).
% 2.25/2.50  thf('104', plain,
% 2.25/2.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50         = (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('simplify', [status(thm)], ['103'])).
% 2.25/2.50  thf('105', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('106', plain,
% 2.25/2.50      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50        (k1_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['65', '66', '104', '105'])).
% 2.25/2.50  thf('107', plain,
% 2.25/2.50      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ 
% 2.25/2.50         (k1_relat_1 @ sk_C))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['0', '106'])).
% 2.25/2.50  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('109', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('110', plain,
% 2.25/2.50      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 2.25/2.50        (k1_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.25/2.50  thf(d1_funct_2, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.25/2.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.25/2.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.25/2.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.25/2.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.25/2.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.25/2.50  thf(zf_stmt_1, axiom,
% 2.25/2.50    (![C:$i,B:$i,A:$i]:
% 2.25/2.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.25/2.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.25/2.50  thf('111', plain,
% 2.25/2.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.25/2.50         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 2.25/2.50          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 2.25/2.50          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.25/2.50  thf('112', plain,
% 2.25/2.50      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50           (k2_relat_1 @ sk_C))
% 2.25/2.50        | ((k2_relat_1 @ sk_C)
% 2.25/2.50            = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50               (k2_funct_1 @ sk_C))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['110', '111'])).
% 2.25/2.50  thf(zf_stmt_2, axiom,
% 2.25/2.50    (![B:$i,A:$i]:
% 2.25/2.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.25/2.50       ( zip_tseitin_0 @ B @ A ) ))).
% 2.25/2.50  thf('113', plain,
% 2.25/2.50      (![X24 : $i, X25 : $i]:
% 2.25/2.50         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.25/2.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.25/2.50  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.25/2.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.25/2.50  thf('115', plain,
% 2.25/2.50      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['113', '114'])).
% 2.25/2.50  thf(fc8_relat_1, axiom,
% 2.25/2.50    (![A:$i]:
% 2.25/2.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 2.25/2.50       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 2.25/2.50  thf('116', plain,
% 2.25/2.50      (![X10 : $i]:
% 2.25/2.50         (~ (v1_xboole_0 @ (k1_relat_1 @ X10))
% 2.25/2.50          | ~ (v1_relat_1 @ X10)
% 2.25/2.50          | (v1_xboole_0 @ X10))),
% 2.25/2.50      inference('cnf', [status(esa)], [fc8_relat_1])).
% 2.25/2.50  thf('117', plain,
% 2.25/2.50      (![X0 : $i, X1 : $i]:
% 2.25/2.50         ((zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 2.25/2.50          | (v1_xboole_0 @ X0)
% 2.25/2.50          | ~ (v1_relat_1 @ X0))),
% 2.25/2.50      inference('sup-', [status(thm)], ['115', '116'])).
% 2.25/2.50  thf('118', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('119', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['6', '52'])).
% 2.25/2.50  thf('120', plain,
% 2.25/2.50      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.25/2.50         ((m1_subset_1 @ (k2_tops_2 @ X42 @ X43 @ X44) @ 
% 2.25/2.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 2.25/2.50          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.25/2.50          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 2.25/2.50          | ~ (v1_funct_1 @ X44))),
% 2.25/2.50      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 2.25/2.50  thf('121', plain,
% 2.25/2.50      ((~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | (m1_subset_1 @ 
% 2.25/2.50           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C) @ 
% 2.25/2.50           (k1_zfmisc_1 @ 
% 2.25/2.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C)))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['119', '120'])).
% 2.25/2.50  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('123', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['61', '62'])).
% 2.25/2.50  thf('124', plain,
% 2.25/2.50      ((m1_subset_1 @ 
% 2.25/2.50        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['121', '122', '123'])).
% 2.25/2.50  thf('125', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('126', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['6', '52'])).
% 2.25/2.50  thf('127', plain,
% 2.25/2.50      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.50         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 2.25/2.50          | ~ (v2_funct_1 @ X41)
% 2.25/2.50          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 2.25/2.50          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 2.25/2.50          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 2.25/2.50          | ~ (v1_funct_1 @ X41))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.25/2.50  thf('128', plain,
% 2.25/2.50      ((~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50            = (k2_funct_1 @ sk_C))
% 2.25/2.50        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.50        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50            != (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['126', '127'])).
% 2.25/2.50  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('130', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['61', '62'])).
% 2.25/2.50  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('132', plain,
% 2.25/2.50      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50          = (k2_funct_1 @ sk_C))
% 2.25/2.50        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50            != (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 2.25/2.50  thf('133', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['4', '5'])).
% 2.25/2.50  thf('134', plain,
% 2.25/2.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.25/2.50         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.25/2.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.25/2.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.25/2.50  thf('135', plain,
% 2.25/2.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['133', '134'])).
% 2.25/2.50  thf('136', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('137', plain,
% 2.25/2.50      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['135', '136'])).
% 2.25/2.50  thf('138', plain,
% 2.25/2.50      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50          = (k2_funct_1 @ sk_C))
% 2.25/2.50        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('demod', [status(thm)], ['132', '137'])).
% 2.25/2.50  thf('139', plain,
% 2.25/2.50      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1)
% 2.25/2.50        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50            = (k2_funct_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['125', '138'])).
% 2.25/2.50  thf('140', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('141', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('142', plain,
% 2.25/2.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 2.25/2.50        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50            = (k2_funct_1 @ sk_C)))),
% 2.25/2.50      inference('demod', [status(thm)], ['139', '140', '141'])).
% 2.25/2.50  thf('143', plain,
% 2.25/2.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)
% 2.25/2.50         = (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('simplify', [status(thm)], ['142'])).
% 2.25/2.50  thf('144', plain,
% 2.25/2.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['124', '143'])).
% 2.25/2.50  thf('145', plain,
% 2.25/2.50      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50         (k1_zfmisc_1 @ 
% 2.25/2.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['118', '144'])).
% 2.25/2.50  thf('146', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('147', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('148', plain,
% 2.25/2.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['145', '146', '147'])).
% 2.25/2.50  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.25/2.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.25/2.50  thf(zf_stmt_5, axiom,
% 2.25/2.50    (![A:$i,B:$i,C:$i]:
% 2.25/2.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.25/2.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.25/2.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.25/2.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.25/2.50  thf('149', plain,
% 2.25/2.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.25/2.50         (~ (zip_tseitin_0 @ X29 @ X30)
% 2.25/2.50          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 2.25/2.50          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.25/2.50  thf('150', plain,
% 2.25/2.50      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50         (k2_relat_1 @ sk_C))
% 2.25/2.50        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['148', '149'])).
% 2.25/2.50  thf('151', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.50        | (v1_xboole_0 @ sk_C)
% 2.25/2.50        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50           (k2_relat_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['117', '150'])).
% 2.25/2.50  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('153', plain,
% 2.25/2.50      (((v1_xboole_0 @ sk_C)
% 2.25/2.50        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50           (k2_relat_1 @ sk_C)))),
% 2.25/2.50      inference('demod', [status(thm)], ['151', '152'])).
% 2.25/2.50  thf(fc11_relat_1, axiom,
% 2.25/2.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 2.25/2.50  thf('154', plain,
% 2.25/2.50      (![X9 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 2.25/2.50      inference('cnf', [status(esa)], [fc11_relat_1])).
% 2.25/2.50  thf('155', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('clc', [status(thm)], ['37', '38'])).
% 2.25/2.50  thf('156', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['154', '155'])).
% 2.25/2.50  thf('157', plain,
% 2.25/2.50      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50        (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('clc', [status(thm)], ['153', '156'])).
% 2.25/2.50  thf('158', plain,
% 2.25/2.50      (((k2_relat_1 @ sk_C)
% 2.25/2.50         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50            (k2_funct_1 @ sk_C)))),
% 2.25/2.50      inference('demod', [status(thm)], ['112', '157'])).
% 2.25/2.50  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('160', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('161', plain,
% 2.25/2.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50            != (k2_struct_0 @ sk_A)))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('162', plain,
% 2.25/2.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_B_1)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('split', [status(esa)], ['161'])).
% 2.25/2.50  thf('163', plain,
% 2.25/2.50      (((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50           != (k2_struct_0 @ sk_B_1))
% 2.25/2.50         | ~ (l1_struct_0 @ sk_B_1)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['160', '162'])).
% 2.25/2.50  thf('164', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('165', plain,
% 2.25/2.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_B_1)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['163', '164'])).
% 2.25/2.50  thf('166', plain,
% 2.25/2.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_B_1)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['159', '165'])).
% 2.25/2.50  thf('167', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('168', plain,
% 2.25/2.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.25/2.50          != (k2_relat_1 @ sk_C)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['166', '167'])).
% 2.25/2.50  thf('169', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.25/2.50      inference('clc', [status(thm)], ['29', '39'])).
% 2.25/2.50  thf('170', plain,
% 2.25/2.50      (![X32 : $i, X33 : $i]:
% 2.25/2.50         (~ (v1_partfun1 @ X33 @ X32)
% 2.25/2.50          | ((k1_relat_1 @ X33) = (X32))
% 2.25/2.50          | ~ (v4_relat_1 @ X33 @ X32)
% 2.25/2.50          | ~ (v1_relat_1 @ X33))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.25/2.50  thf('171', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.50        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.25/2.50        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['169', '170'])).
% 2.25/2.50  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('173', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('174', plain,
% 2.25/2.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.25/2.50         ((v4_relat_1 @ X15 @ X16)
% 2.25/2.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.25/2.50  thf('175', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.25/2.50      inference('sup-', [status(thm)], ['173', '174'])).
% 2.25/2.50  thf('176', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['171', '172', '175'])).
% 2.25/2.50  thf('177', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['171', '172', '175'])).
% 2.25/2.50  thf('178', plain,
% 2.25/2.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50         = (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('simplify', [status(thm)], ['103'])).
% 2.25/2.50  thf('179', plain,
% 2.25/2.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['168', '176', '177', '178'])).
% 2.25/2.50  thf('180', plain,
% 2.25/2.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['124', '143'])).
% 2.25/2.50  thf('181', plain,
% 2.25/2.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.25/2.50         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.25/2.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.25/2.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.25/2.50  thf('182', plain,
% 2.25/2.50      (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['180', '181'])).
% 2.25/2.50  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf(t55_funct_1, axiom,
% 2.25/2.50    (![A:$i]:
% 2.25/2.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.50       ( ( v2_funct_1 @ A ) =>
% 2.25/2.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.25/2.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.25/2.50  thf('184', plain,
% 2.25/2.50      (![X11 : $i]:
% 2.25/2.50         (~ (v2_funct_1 @ X11)
% 2.25/2.50          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 2.25/2.50          | ~ (v1_funct_1 @ X11)
% 2.25/2.50          | ~ (v1_relat_1 @ X11))),
% 2.25/2.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.50  thf('185', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.50        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.50        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['183', '184'])).
% 2.25/2.50  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('187', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.50        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['185', '186'])).
% 2.25/2.50  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('189', plain,
% 2.25/2.50      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.25/2.50      inference('demod', [status(thm)], ['187', '188'])).
% 2.25/2.50  thf('190', plain,
% 2.25/2.50      (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['182', '189'])).
% 2.25/2.50  thf('191', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('192', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('193', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('194', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_A)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('split', [status(esa)], ['161'])).
% 2.25/2.50  thf('195', plain,
% 2.25/2.50      (((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 2.25/2.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50           != (k2_struct_0 @ sk_A))
% 2.25/2.50         | ~ (l1_struct_0 @ sk_A)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['193', '194'])).
% 2.25/2.50  thf('196', plain, ((l1_struct_0 @ sk_A)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('197', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_A)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('demod', [status(thm)], ['195', '196'])).
% 2.25/2.50  thf('198', plain,
% 2.25/2.50      (((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 2.25/2.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50           != (k2_struct_0 @ sk_A))
% 2.25/2.50         | ~ (l1_struct_0 @ sk_B_1)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['192', '197'])).
% 2.25/2.50  thf('199', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('200', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_A)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('demod', [status(thm)], ['198', '199'])).
% 2.25/2.50  thf('201', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          != (k2_struct_0 @ sk_A)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['191', '200'])).
% 2.25/2.50  thf('202', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('203', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['45', '48', '51'])).
% 2.25/2.50  thf('204', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.25/2.50          != (k1_relat_1 @ sk_C)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('demod', [status(thm)], ['201', '202', '203'])).
% 2.25/2.50  thf('205', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.25/2.50      inference('demod', [status(thm)], ['171', '172', '175'])).
% 2.25/2.50  thf('206', plain,
% 2.25/2.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50         = (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('simplify', [status(thm)], ['103'])).
% 2.25/2.50  thf('207', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('demod', [status(thm)], ['204', '205', '206'])).
% 2.25/2.50  thf('208', plain,
% 2.25/2.50      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 2.25/2.50         <= (~
% 2.25/2.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50                 sk_C))
% 2.25/2.50                = (k2_struct_0 @ sk_A))))),
% 2.25/2.50      inference('sup-', [status(thm)], ['190', '207'])).
% 2.25/2.50  thf('209', plain,
% 2.25/2.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          = (k2_struct_0 @ sk_A)))),
% 2.25/2.50      inference('simplify', [status(thm)], ['208'])).
% 2.25/2.50  thf('210', plain,
% 2.25/2.50      (~
% 2.25/2.50       (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          = (k2_struct_0 @ sk_B_1))) | 
% 2.25/2.50       ~
% 2.25/2.50       (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          = (k2_struct_0 @ sk_A)))),
% 2.25/2.50      inference('split', [status(esa)], ['161'])).
% 2.25/2.50  thf('211', plain,
% 2.25/2.50      (~
% 2.25/2.50       (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50          = (k2_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('sat_resolution*', [status(thm)], ['209', '210'])).
% 2.25/2.50  thf('212', plain,
% 2.25/2.50      (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('simpl_trail', [status(thm)], ['179', '211'])).
% 2.25/2.50  thf('213', plain,
% 2.25/2.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['124', '143'])).
% 2.25/2.50  thf('214', plain,
% 2.25/2.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.25/2.50         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.25/2.50          | (v1_partfun1 @ X21 @ X22)
% 2.25/2.50          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 2.25/2.50          | ~ (v1_funct_1 @ X21)
% 2.25/2.50          | (v1_xboole_0 @ X23))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc5_funct_2])).
% 2.25/2.50  thf('215', plain,
% 2.25/2.50      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 2.25/2.50        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.50        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50             (k1_relat_1 @ sk_C))
% 2.25/2.50        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['213', '214'])).
% 2.25/2.50  thf('216', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('217', plain,
% 2.25/2.50      ((m1_subset_1 @ sk_C @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.50      inference('demod', [status(thm)], ['6', '52'])).
% 2.25/2.50  thf('218', plain,
% 2.25/2.50      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.25/2.50         ((v1_funct_1 @ (k2_tops_2 @ X42 @ X43 @ X44))
% 2.25/2.50          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.25/2.50          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 2.25/2.50          | ~ (v1_funct_1 @ X44))),
% 2.25/2.50      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 2.25/2.50  thf('219', plain,
% 2.25/2.50      ((~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | (v1_funct_1 @ 
% 2.25/2.50           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['217', '218'])).
% 2.25/2.50  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('221', plain,
% 2.25/2.50      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('demod', [status(thm)], ['61', '62'])).
% 2.25/2.50  thf('222', plain,
% 2.25/2.50      ((v1_funct_1 @ 
% 2.25/2.50        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['219', '220', '221'])).
% 2.25/2.50  thf('223', plain,
% 2.25/2.50      (((v1_funct_1 @ 
% 2.25/2.50         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['216', '222'])).
% 2.25/2.50  thf('224', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('225', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('226', plain,
% 2.25/2.50      ((v1_funct_1 @ 
% 2.25/2.50        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['223', '224', '225'])).
% 2.25/2.50  thf('227', plain,
% 2.25/2.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.25/2.50         = (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('simplify', [status(thm)], ['103'])).
% 2.25/2.50  thf('228', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['226', '227'])).
% 2.25/2.50  thf('229', plain,
% 2.25/2.50      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.50        (k1_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['65', '66', '104', '105'])).
% 2.25/2.50  thf('230', plain,
% 2.25/2.50      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 2.25/2.50        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('demod', [status(thm)], ['215', '228', '229'])).
% 2.25/2.50  thf('231', plain,
% 2.25/2.50      (![X32 : $i, X33 : $i]:
% 2.25/2.50         (~ (v1_partfun1 @ X33 @ X32)
% 2.25/2.50          | ((k1_relat_1 @ X33) = (X32))
% 2.25/2.50          | ~ (v4_relat_1 @ X33 @ X32)
% 2.25/2.50          | ~ (v1_relat_1 @ X33))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.25/2.50  thf('232', plain,
% 2.25/2.50      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 2.25/2.50        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.50        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['230', '231'])).
% 2.25/2.50  thf('233', plain,
% 2.25/2.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['124', '143'])).
% 2.25/2.50  thf('234', plain,
% 2.25/2.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.25/2.50         ((v1_relat_1 @ X12)
% 2.25/2.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.25/2.50  thf('235', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['233', '234'])).
% 2.25/2.50  thf('236', plain,
% 2.25/2.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50        (k1_zfmisc_1 @ 
% 2.25/2.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C))))),
% 2.25/2.50      inference('demod', [status(thm)], ['124', '143'])).
% 2.25/2.50  thf('237', plain,
% 2.25/2.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.25/2.50         ((v4_relat_1 @ X15 @ X16)
% 2.25/2.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.25/2.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.25/2.50  thf('238', plain,
% 2.25/2.50      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup-', [status(thm)], ['236', '237'])).
% 2.25/2.50  thf('239', plain,
% 2.25/2.50      (![X11 : $i]:
% 2.25/2.50         (~ (v2_funct_1 @ X11)
% 2.25/2.50          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 2.25/2.50          | ~ (v1_funct_1 @ X11)
% 2.25/2.50          | ~ (v1_relat_1 @ X11))),
% 2.25/2.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.50  thf('240', plain,
% 2.25/2.50      (![X34 : $i]:
% 2.25/2.50         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 2.25/2.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.25/2.50  thf('241', plain,
% 2.25/2.50      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup-', [status(thm)], ['236', '237'])).
% 2.25/2.50  thf('242', plain,
% 2.25/2.50      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B_1))
% 2.25/2.50        | ~ (l1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['240', '241'])).
% 2.25/2.50  thf('243', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('sup+', [status(thm)], ['15', '16'])).
% 2.25/2.50  thf('244', plain, ((l1_struct_0 @ sk_B_1)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('245', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['242', '243', '244'])).
% 2.25/2.50  thf('246', plain,
% 2.25/2.50      (![X11 : $i]:
% 2.25/2.50         (~ (v2_funct_1 @ X11)
% 2.25/2.50          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 2.25/2.50          | ~ (v1_funct_1 @ X11)
% 2.25/2.50          | ~ (v1_relat_1 @ X11))),
% 2.25/2.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.50  thf('247', plain,
% 2.25/2.50      (![X32 : $i, X33 : $i]:
% 2.25/2.50         (((k1_relat_1 @ X33) != (X32))
% 2.25/2.50          | (v1_partfun1 @ X33 @ X32)
% 2.25/2.50          | ~ (v4_relat_1 @ X33 @ X32)
% 2.25/2.50          | ~ (v1_relat_1 @ X33))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.25/2.50  thf('248', plain,
% 2.25/2.50      (![X33 : $i]:
% 2.25/2.50         (~ (v1_relat_1 @ X33)
% 2.25/2.50          | ~ (v4_relat_1 @ X33 @ (k1_relat_1 @ X33))
% 2.25/2.50          | (v1_partfun1 @ X33 @ (k1_relat_1 @ X33)))),
% 2.25/2.50      inference('simplify', [status(thm)], ['247'])).
% 2.25/2.50  thf('249', plain,
% 2.25/2.50      (![X0 : $i]:
% 2.25/2.50         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.25/2.50          | ~ (v1_relat_1 @ X0)
% 2.25/2.50          | ~ (v1_funct_1 @ X0)
% 2.25/2.50          | ~ (v2_funct_1 @ X0)
% 2.25/2.50          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.25/2.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['246', '248'])).
% 2.25/2.50  thf('250', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.50        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 2.25/2.50           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.50        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v1_relat_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['245', '249'])).
% 2.25/2.50  thf('251', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['233', '234'])).
% 2.25/2.50  thf('252', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('255', plain,
% 2.25/2.50      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.25/2.50      inference('demod', [status(thm)], ['250', '251', '252', '253', '254'])).
% 2.25/2.50  thf('256', plain,
% 2.25/2.50      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.50        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.50        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.50      inference('sup+', [status(thm)], ['239', '255'])).
% 2.25/2.50  thf('257', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('259', plain, ((v2_funct_1 @ sk_C)),
% 2.25/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.50  thf('260', plain,
% 2.25/2.50      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 2.25/2.50  thf('261', plain,
% 2.25/2.50      (![X32 : $i, X33 : $i]:
% 2.25/2.50         (~ (v1_partfun1 @ X33 @ X32)
% 2.25/2.50          | ((k1_relat_1 @ X33) = (X32))
% 2.25/2.50          | ~ (v4_relat_1 @ X33 @ X32)
% 2.25/2.50          | ~ (v1_relat_1 @ X33))),
% 2.25/2.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.25/2.50  thf('262', plain,
% 2.25/2.50      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.50        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.25/2.50        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 2.25/2.50      inference('sup-', [status(thm)], ['260', '261'])).
% 2.25/2.50  thf('263', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['233', '234'])).
% 2.25/2.50  thf('264', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['242', '243', '244'])).
% 2.25/2.50  thf('265', plain,
% 2.25/2.50      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['262', '263', '264'])).
% 2.25/2.50  thf('266', plain,
% 2.25/2.50      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 2.25/2.50        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B_1)))),
% 2.25/2.50      inference('demod', [status(thm)], ['232', '235', '238', '265'])).
% 2.25/2.50  thf('267', plain,
% 2.25/2.50      (![X10 : $i]:
% 2.25/2.50         (~ (v1_xboole_0 @ (k1_relat_1 @ X10))
% 2.25/2.50          | ~ (v1_relat_1 @ X10)
% 2.25/2.50          | (v1_xboole_0 @ X10))),
% 2.25/2.50      inference('cnf', [status(esa)], [fc8_relat_1])).
% 2.25/2.50  thf('268', plain,
% 2.25/2.50      ((((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B_1))
% 2.25/2.50        | (v1_xboole_0 @ sk_C)
% 2.25/2.50        | ~ (v1_relat_1 @ sk_C))),
% 2.25/2.50      inference('sup-', [status(thm)], ['266', '267'])).
% 2.25/2.50  thf('269', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['46', '47'])).
% 2.25/2.50  thf('270', plain,
% 2.25/2.50      ((((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B_1)) | (v1_xboole_0 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['268', '269'])).
% 2.25/2.50  thf('271', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.25/2.50      inference('sup-', [status(thm)], ['154', '155'])).
% 2.25/2.50  thf('272', plain, (((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B_1))),
% 2.25/2.50      inference('clc', [status(thm)], ['270', '271'])).
% 2.25/2.50  thf('273', plain,
% 2.25/2.50      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.25/2.50         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 2.25/2.50      inference('demod', [status(thm)], ['212', '272'])).
% 2.25/2.50  thf('274', plain, ($false),
% 2.25/2.50      inference('simplify_reflect-', [status(thm)], ['158', '273'])).
% 2.25/2.50  
% 2.25/2.50  % SZS output end Refutation
% 2.25/2.50  
% 2.25/2.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
