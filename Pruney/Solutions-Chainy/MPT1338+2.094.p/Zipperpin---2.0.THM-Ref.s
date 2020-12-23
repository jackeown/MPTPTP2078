%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bY3UAr4A76

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:03 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 606 expanded)
%              Number of leaves         :   41 ( 192 expanded)
%              Depth                    :   17
%              Number of atoms          : 2109 (16264 expanded)
%              Number of equality atoms :  163 ( 913 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

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

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','58','59','71'])).

thf('73',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('90',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

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

thf('99',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101','108','116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','121'])).

thf('123',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('127',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','128','129','130'])).

thf('132',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('134',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('135',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('140',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139'])).

thf('141',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['77'])).

thf('145',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('154',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','154'])).

thf('156',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('157',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('158',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','158'])).

thf('160',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['126','127'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['77'])).

thf('167',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['165','166'])).

thf('168',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['131','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','168'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('170',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('171',plain,(
    $false ),
    inference(demod,[status(thm)],['10','169','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bY3UAr4A76
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 275 iterations in 0.537s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.99  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.76/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.99  thf(t62_tops_2, conjecture,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_struct_0 @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                 ( m1_subset_1 @
% 0.76/0.99                   C @ 
% 0.76/0.99                   ( k1_zfmisc_1 @
% 0.76/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99               ( ( ( ( k2_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                   ( v2_funct_1 @ C ) ) =>
% 0.76/0.99                 ( ( ( k1_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.99                       ( k2_tops_2 @
% 0.76/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                   ( ( k2_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.99                       ( k2_tops_2 @
% 0.76/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.99                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i]:
% 0.76/0.99        ( ( l1_struct_0 @ A ) =>
% 0.76/0.99          ( ![B:$i]:
% 0.76/0.99            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.99              ( ![C:$i]:
% 0.76/0.99                ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                    ( v1_funct_2 @
% 0.76/0.99                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                    ( m1_subset_1 @
% 0.76/0.99                      C @ 
% 0.76/0.99                      ( k1_zfmisc_1 @
% 0.76/0.99                        ( k2_zfmisc_1 @
% 0.76/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                  ( ( ( ( k2_relset_1 @
% 0.76/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                      ( v2_funct_1 @ C ) ) =>
% 0.76/0.99                    ( ( ( k1_relset_1 @
% 0.76/0.99                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.99                          ( k2_tops_2 @
% 0.76/0.99                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                      ( ( k2_relset_1 @
% 0.76/0.99                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.99                          ( k2_tops_2 @
% 0.76/0.99                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.99                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.99         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.76/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.99  thf('2', plain,
% 0.76/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k2_relat_1 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf(fc5_struct_0, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.99       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.76/0.99  thf('5', plain,
% 0.76/0.99      (![X23 : $i]:
% 0.76/0.99         (~ (v1_xboole_0 @ (k2_struct_0 @ X23))
% 0.76/0.99          | ~ (l1_struct_0 @ X23)
% 0.76/0.99          | (v2_struct_0 @ X23))),
% 0.76/0.99      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.76/0.99        | (v2_struct_0 @ sk_B)
% 0.76/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.99  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('8', plain,
% 0.76/0.99      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.99  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.76/0.99      inference('clc', [status(thm)], ['8', '9'])).
% 0.76/0.99  thf(d3_struct_0, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.76/0.99  thf('11', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('12', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf(d1_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_1, axiom,
% 0.76/0.99    (![B:$i,A:$i]:
% 0.76/0.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.99       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.99  thf('13', plain,
% 0.76/0.99      (![X11 : $i, X12 : $i]:
% 0.76/0.99         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.99  thf('14', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_3, axiom,
% 0.76/0.99    (![C:$i,B:$i,A:$i]:
% 0.76/0.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_5, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.99         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.76/0.99          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.76/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.99  thf('16', plain,
% 0.76/0.99      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.99        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.99  thf('17', plain,
% 0.76/0.99      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.99        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['13', '16'])).
% 0.76/0.99  thf('18', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('19', plain,
% 0.76/0.99      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.99         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.76/0.99          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.76/0.99          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.99        | ((u1_struct_0 @ sk_A)
% 0.76/0.99            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.99  thf('21', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.99  thf('22', plain,
% 0.76/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.99         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.76/0.99          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k1_relat_1 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('24', plain,
% 0.76/0.99      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.99        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.99      inference('demod', [status(thm)], ['20', '23'])).
% 0.76/0.99  thf('25', plain,
% 0.76/0.99      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.99        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['17', '24'])).
% 0.76/0.99  thf('26', plain,
% 0.76/0.99      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_B)
% 0.76/0.99        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.99      inference('sup+', [status(thm)], ['12', '25'])).
% 0.76/0.99  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.76/0.99        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.99      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.76/0.99  thf('30', plain,
% 0.76/0.99      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_A)
% 0.76/0.99        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.76/0.99      inference('sup+', [status(thm)], ['11', '29'])).
% 0.76/0.99  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('32', plain,
% 0.76/0.99      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.76/0.99        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.76/0.99      inference('demod', [status(thm)], ['30', '31'])).
% 0.76/0.99  thf(t55_funct_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.99       ( ( v2_funct_1 @ A ) =>
% 0.76/0.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.76/0.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.76/0.99  thf('33', plain,
% 0.76/0.99      (![X4 : $i]:
% 0.76/0.99         (~ (v2_funct_1 @ X4)
% 0.76/0.99          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.76/0.99          | ~ (v1_funct_1 @ X4)
% 0.76/0.99          | ~ (v1_relat_1 @ X4))),
% 0.76/0.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('35', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('36', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('37', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C @ 
% 0.76/0.99         (k1_zfmisc_1 @ 
% 0.76/0.99          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.99      inference('sup+', [status(thm)], ['35', '36'])).
% 0.76/0.99  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('39', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('demod', [status(thm)], ['37', '38'])).
% 0.76/0.99  thf('40', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C @ 
% 0.76/0.99         (k1_zfmisc_1 @ 
% 0.76/0.99          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['34', '39'])).
% 0.76/0.99  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.99      inference('demod', [status(thm)], ['40', '41'])).
% 0.76/0.99  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.76/0.99      inference('demod', [status(thm)], ['42', '43'])).
% 0.76/0.99  thf(d4_tops_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.99       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.76/0.99         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.99         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.76/0.99          | ~ (v2_funct_1 @ X26)
% 0.76/0.99          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.76/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.76/0.99          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.76/0.99          | ~ (v1_funct_1 @ X26))),
% 0.76/0.99      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.76/0.99  thf('46', plain,
% 0.76/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.76/0.99        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.99            = (k2_funct_1 @ sk_C))
% 0.76/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.99        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.99            != (k2_relat_1 @ sk_C)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/0.99  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('50', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('51', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.99      inference('sup+', [status(thm)], ['49', '50'])).
% 0.76/0.99  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['51', '52'])).
% 0.76/0.99  thf('54', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['48', '53'])).
% 0.76/0.99  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('56', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.99  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('58', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['56', '57'])).
% 0.76/0.99  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('61', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('62', plain,
% 0.76/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('63', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.99      inference('sup+', [status(thm)], ['61', '62'])).
% 0.76/0.99  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('65', plain,
% 0.76/0.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.99  thf('66', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['60', '65'])).
% 0.76/0.99  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('68', plain,
% 0.76/0.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['66', '67'])).
% 0.76/0.99  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('71', plain,
% 0.76/0.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.99         = (k2_relat_1 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.76/0.99  thf('72', plain,
% 0.76/0.99      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.99          = (k2_funct_1 @ sk_C))
% 0.76/0.99        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.76/0.99      inference('demod', [status(thm)], ['46', '47', '58', '59', '71'])).
% 0.76/0.99  thf('73', plain,
% 0.76/0.99      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.99         = (k2_funct_1 @ sk_C))),
% 0.76/0.99      inference('simplify', [status(thm)], ['72'])).
% 0.76/0.99  thf('74', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('75', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('76', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('77', plain,
% 0.76/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99          != (k2_struct_0 @ sk_B))
% 0.76/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99            != (k2_struct_0 @ sk_A)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('78', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99          != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('split', [status(esa)], ['77'])).
% 0.76/0.99  thf('79', plain,
% 0.76/0.99      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99           != (k2_struct_0 @ sk_A))
% 0.76/0.99         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['76', '78'])).
% 0.76/0.99  thf('80', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('81', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99          != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('demod', [status(thm)], ['79', '80'])).
% 0.76/0.99  thf('82', plain,
% 0.76/0.99      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99           != (k2_struct_0 @ sk_A))
% 0.76/0.99         | ~ (l1_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['75', '81'])).
% 0.76/0.99  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('84', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99          != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('demod', [status(thm)], ['82', '83'])).
% 0.76/0.99  thf('85', plain,
% 0.76/0.99      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99           != (k2_struct_0 @ sk_A))
% 0.76/0.99         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['74', '84'])).
% 0.76/0.99  thf('86', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('87', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99          != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('demod', [status(thm)], ['85', '86'])).
% 0.76/0.99  thf('88', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('90', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.76/0.99          != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.76/0.99  thf('91', plain,
% 0.76/0.99      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.99                = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['73', '90'])).
% 0.76/0.99  thf('92', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.99  thf('93', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('94', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C @ 
% 0.76/0.99         (k1_zfmisc_1 @ 
% 0.76/0.99          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.76/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['92', '93'])).
% 0.76/0.99  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('96', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.99      inference('demod', [status(thm)], ['94', '95'])).
% 0.76/0.99  thf('97', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('98', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.76/0.99      inference('demod', [status(thm)], ['96', '97'])).
% 0.76/0.99  thf(t31_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.99       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.76/0.99         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.76/0.99           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.76/0.99           ( m1_subset_1 @
% 0.76/0.99             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.76/0.99  thf('99', plain,
% 0.76/0.99      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.99         (~ (v2_funct_1 @ X19)
% 0.76/0.99          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 0.76/0.99          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 0.76/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.76/0.99          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.76/0.99          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 0.76/0.99          | ~ (v1_funct_1 @ X19))),
% 0.76/0.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.76/0.99  thf('100', plain,
% 0.76/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.76/0.99        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.99           (k1_zfmisc_1 @ 
% 0.76/0.99            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.76/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.99            != (k2_relat_1 @ sk_C))
% 0.76/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['98', '99'])).
% 0.76/0.99  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('102', plain,
% 0.76/0.99      (![X22 : $i]:
% 0.76/0.99         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/1.00  thf('103', plain,
% 0.76/1.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('104', plain,
% 0.76/1.00      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/1.00        | ~ (l1_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['102', '103'])).
% 0.76/1.00  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('106', plain,
% 0.76/1.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('demod', [status(thm)], ['104', '105'])).
% 0.76/1.00  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/1.00  thf('108', plain,
% 0.76/1.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.76/1.00      inference('demod', [status(thm)], ['106', '107'])).
% 0.76/1.00  thf('109', plain,
% 0.76/1.00      (![X22 : $i]:
% 0.76/1.00         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/1.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/1.00  thf('110', plain,
% 0.76/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/1.00         = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('111', plain,
% 0.76/1.00      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/1.00          = (k2_struct_0 @ sk_B))
% 0.76/1.00        | ~ (l1_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['109', '110'])).
% 0.76/1.00  thf('112', plain, ((l1_struct_0 @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('113', plain,
% 0.76/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/1.00         = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('demod', [status(thm)], ['111', '112'])).
% 0.76/1.00  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/1.00  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/1.00  thf('116', plain,
% 0.76/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/1.00         = (k2_relat_1 @ sk_C))),
% 0.76/1.00      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.76/1.00  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('118', plain,
% 0.76/1.00      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/1.00         (k1_zfmisc_1 @ 
% 0.76/1.00          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.76/1.00        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.76/1.00      inference('demod', [status(thm)], ['100', '101', '108', '116', '117'])).
% 0.76/1.00  thf('119', plain,
% 0.76/1.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/1.00        (k1_zfmisc_1 @ 
% 0.76/1.00         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.76/1.00      inference('simplify', [status(thm)], ['118'])).
% 0.76/1.00  thf('120', plain,
% 0.76/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/1.00         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.76/1.00          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/1.00  thf('121', plain,
% 0.76/1.00      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['119', '120'])).
% 0.76/1.00  thf('122', plain,
% 0.76/1.00      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_A))))),
% 0.76/1.00      inference('demod', [status(thm)], ['91', '121'])).
% 0.76/1.00  thf('123', plain,
% 0.76/1.00      (((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.76/1.00         | ~ (v1_relat_1 @ sk_C)
% 0.76/1.00         | ~ (v1_funct_1 @ sk_C)
% 0.76/1.00         | ~ (v2_funct_1 @ sk_C)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_A))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['33', '122'])).
% 0.76/1.00  thf('124', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_C @ 
% 0.76/1.00        (k1_zfmisc_1 @ 
% 0.76/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf(cc2_relat_1, axiom,
% 0.76/1.00    (![A:$i]:
% 0.76/1.00     ( ( v1_relat_1 @ A ) =>
% 0.76/1.00       ( ![B:$i]:
% 0.76/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/1.00  thf('125', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.76/1.00          | (v1_relat_1 @ X0)
% 0.76/1.00          | ~ (v1_relat_1 @ X1))),
% 0.76/1.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/1.00  thf('126', plain,
% 0.76/1.00      ((~ (v1_relat_1 @ 
% 0.76/1.00           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.76/1.00        | (v1_relat_1 @ sk_C))),
% 0.76/1.00      inference('sup-', [status(thm)], ['124', '125'])).
% 0.76/1.00  thf(fc6_relat_1, axiom,
% 0.76/1.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/1.00  thf('127', plain,
% 0.76/1.00      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.76/1.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/1.00  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 0.76/1.00      inference('demod', [status(thm)], ['126', '127'])).
% 0.76/1.00  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('131', plain,
% 0.76/1.00      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_A))))),
% 0.76/1.00      inference('demod', [status(thm)], ['123', '128', '129', '130'])).
% 0.76/1.00  thf('132', plain,
% 0.76/1.00      (![X4 : $i]:
% 0.76/1.00         (~ (v2_funct_1 @ X4)
% 0.76/1.00          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.76/1.00          | ~ (v1_funct_1 @ X4)
% 0.76/1.00          | ~ (v1_relat_1 @ X4))),
% 0.76/1.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.76/1.00  thf('133', plain,
% 0.76/1.00      ((m1_subset_1 @ sk_C @ 
% 0.76/1.00        (k1_zfmisc_1 @ 
% 0.76/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.76/1.00      inference('demod', [status(thm)], ['96', '97'])).
% 0.76/1.00  thf('134', plain,
% 0.76/1.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/1.00         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.76/1.00          | ~ (v2_funct_1 @ X26)
% 0.76/1.00          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.76/1.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.76/1.00          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.76/1.00          | ~ (v1_funct_1 @ X26))),
% 0.76/1.00      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.76/1.00  thf('135', plain,
% 0.76/1.00      ((~ (v1_funct_1 @ sk_C)
% 0.76/1.00        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.76/1.00        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/1.00            = (k2_funct_1 @ sk_C))
% 0.76/1.00        | ~ (v2_funct_1 @ sk_C)
% 0.76/1.00        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/1.00            != (k2_relat_1 @ sk_C)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['133', '134'])).
% 0.76/1.00  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('137', plain,
% 0.76/1.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.76/1.00      inference('demod', [status(thm)], ['106', '107'])).
% 0.76/1.00  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('139', plain,
% 0.76/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/1.00         = (k2_relat_1 @ sk_C))),
% 0.76/1.00      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.76/1.00  thf('140', plain,
% 0.76/1.00      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/1.00          = (k2_funct_1 @ sk_C))
% 0.76/1.00        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.76/1.00      inference('demod', [status(thm)], ['135', '136', '137', '138', '139'])).
% 0.76/1.00  thf('141', plain,
% 0.76/1.00      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/1.00         = (k2_funct_1 @ sk_C))),
% 0.76/1.00      inference('simplify', [status(thm)], ['140'])).
% 0.76/1.00  thf('142', plain,
% 0.76/1.00      (![X22 : $i]:
% 0.76/1.00         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/1.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/1.00  thf('143', plain,
% 0.76/1.00      (![X22 : $i]:
% 0.76/1.00         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/1.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/1.00  thf('144', plain,
% 0.76/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          != (k2_struct_0 @ sk_B)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('split', [status(esa)], ['77'])).
% 0.76/1.00  thf('145', plain,
% 0.76/1.00      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00           != (k2_struct_0 @ sk_B))
% 0.76/1.00         | ~ (l1_struct_0 @ sk_B)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['143', '144'])).
% 0.76/1.00  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('147', plain,
% 0.76/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          != (k2_struct_0 @ sk_B)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('demod', [status(thm)], ['145', '146'])).
% 0.76/1.00  thf('148', plain,
% 0.76/1.00      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00           != (k2_struct_0 @ sk_B))
% 0.76/1.00         | ~ (l1_struct_0 @ sk_B)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['142', '147'])).
% 0.76/1.00  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('150', plain,
% 0.76/1.00      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          != (k2_struct_0 @ sk_B)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('demod', [status(thm)], ['148', '149'])).
% 0.76/1.00  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/1.00  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/1.00  thf('153', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/1.00      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/1.00  thf('154', plain,
% 0.76/1.00      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.76/1.00          != (k2_relat_1 @ sk_C)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 0.76/1.00  thf('155', plain,
% 0.76/1.00      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['141', '154'])).
% 0.76/1.00  thf('156', plain,
% 0.76/1.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/1.00        (k1_zfmisc_1 @ 
% 0.76/1.00         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.76/1.00      inference('simplify', [status(thm)], ['118'])).
% 0.76/1.00  thf('157', plain,
% 0.76/1.00      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.76/1.00         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.76/1.00          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.76/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/1.00  thf('158', plain,
% 0.76/1.00      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['156', '157'])).
% 0.76/1.00  thf('159', plain,
% 0.76/1.00      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('demod', [status(thm)], ['155', '158'])).
% 0.76/1.00  thf('160', plain,
% 0.76/1.00      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.76/1.00         | ~ (v1_relat_1 @ sk_C)
% 0.76/1.00         | ~ (v1_funct_1 @ sk_C)
% 0.76/1.00         | ~ (v2_funct_1 @ sk_C)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['132', '159'])).
% 0.76/1.00  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 0.76/1.00      inference('demod', [status(thm)], ['126', '127'])).
% 0.76/1.00  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('164', plain,
% 0.76/1.00      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.76/1.00         <= (~
% 0.76/1.00             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00                = (k2_struct_0 @ sk_B))))),
% 0.76/1.00      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 0.76/1.00  thf('165', plain,
% 0.76/1.00      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          = (k2_struct_0 @ sk_B)))),
% 0.76/1.00      inference('simplify', [status(thm)], ['164'])).
% 0.76/1.00  thf('166', plain,
% 0.76/1.00      (~
% 0.76/1.00       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          = (k2_struct_0 @ sk_A))) | 
% 0.76/1.00       ~
% 0.76/1.00       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          = (k2_struct_0 @ sk_B)))),
% 0.76/1.00      inference('split', [status(esa)], ['77'])).
% 0.76/1.00  thf('167', plain,
% 0.76/1.00      (~
% 0.76/1.00       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/1.00          = (k2_struct_0 @ sk_A)))),
% 0.76/1.00      inference('sat_resolution*', [status(thm)], ['165', '166'])).
% 0.76/1.00  thf('168', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.76/1.00      inference('simpl_trail', [status(thm)], ['131', '167'])).
% 0.76/1.00  thf('169', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.76/1.00      inference('simplify_reflect-', [status(thm)], ['32', '168'])).
% 0.76/1.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/1.00  thf('170', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/1.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/1.00  thf('171', plain, ($false),
% 0.76/1.00      inference('demod', [status(thm)], ['10', '169', '170'])).
% 0.76/1.00  
% 0.76/1.00  % SZS output end Refutation
% 0.76/1.00  
% 0.84/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
