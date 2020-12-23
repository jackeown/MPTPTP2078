%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2Ycs7eHtB

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:55 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 600 expanded)
%              Number of leaves         :   40 ( 190 expanded)
%              Depth                    :   19
%              Number of atoms          : 2066 (16205 expanded)
%              Number of equality atoms :  161 ( 911 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('125',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('131',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['77'])).

thf('136',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','145'])).

thf('147',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('148',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('149',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','149'])).

thf('151',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('153',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','154','155','156'])).

thf('158',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['77'])).

thf('160',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['158','159'])).

thf('161',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['122','160'])).

thf('162',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','166'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('168',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['10','167','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2Ycs7eHtB
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.27/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.27/1.46  % Solved by: fo/fo7.sh
% 1.27/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.46  % done 347 iterations in 1.002s
% 1.27/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.27/1.46  % SZS output start Refutation
% 1.27/1.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.27/1.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.27/1.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.27/1.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.27/1.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.27/1.46  thf(sk_C_type, type, sk_C: $i).
% 1.27/1.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.27/1.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.27/1.46  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.27/1.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.27/1.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.27/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.27/1.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.27/1.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.27/1.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.27/1.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.27/1.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.27/1.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.27/1.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.27/1.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.27/1.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.27/1.46  thf(t62_tops_2, conjecture,
% 1.27/1.46    (![A:$i]:
% 1.27/1.46     ( ( l1_struct_0 @ A ) =>
% 1.27/1.46       ( ![B:$i]:
% 1.27/1.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.27/1.46           ( ![C:$i]:
% 1.27/1.46             ( ( ( v1_funct_1 @ C ) & 
% 1.27/1.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.27/1.46                 ( m1_subset_1 @
% 1.27/1.46                   C @ 
% 1.27/1.46                   ( k1_zfmisc_1 @
% 1.27/1.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.27/1.46               ( ( ( ( k2_relset_1 @
% 1.27/1.46                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.27/1.46                     ( k2_struct_0 @ B ) ) & 
% 1.27/1.46                   ( v2_funct_1 @ C ) ) =>
% 1.27/1.46                 ( ( ( k1_relset_1 @
% 1.27/1.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.27/1.46                       ( k2_tops_2 @
% 1.27/1.46                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.27/1.46                     ( k2_struct_0 @ B ) ) & 
% 1.27/1.46                   ( ( k2_relset_1 @
% 1.27/1.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.27/1.46                       ( k2_tops_2 @
% 1.27/1.46                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.27/1.46                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.27/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.46    (~( ![A:$i]:
% 1.27/1.46        ( ( l1_struct_0 @ A ) =>
% 1.27/1.46          ( ![B:$i]:
% 1.27/1.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.27/1.46              ( ![C:$i]:
% 1.27/1.46                ( ( ( v1_funct_1 @ C ) & 
% 1.27/1.46                    ( v1_funct_2 @
% 1.27/1.46                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.27/1.46                    ( m1_subset_1 @
% 1.27/1.46                      C @ 
% 1.27/1.46                      ( k1_zfmisc_1 @
% 1.27/1.46                        ( k2_zfmisc_1 @
% 1.27/1.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.27/1.46                  ( ( ( ( k2_relset_1 @
% 1.27/1.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.27/1.46                        ( k2_struct_0 @ B ) ) & 
% 1.27/1.46                      ( v2_funct_1 @ C ) ) =>
% 1.27/1.46                    ( ( ( k1_relset_1 @
% 1.27/1.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.27/1.46                          ( k2_tops_2 @
% 1.27/1.46                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.27/1.46                        ( k2_struct_0 @ B ) ) & 
% 1.27/1.46                      ( ( k2_relset_1 @
% 1.27/1.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.27/1.46                          ( k2_tops_2 @
% 1.27/1.46                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.27/1.46                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.27/1.46    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.27/1.46  thf('0', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(redefinition_k2_relset_1, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.27/1.46  thf('1', plain,
% 1.27/1.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.27/1.46         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 1.27/1.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.27/1.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.27/1.46  thf('2', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('sup-', [status(thm)], ['0', '1'])).
% 1.27/1.46  thf('3', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf(fc5_struct_0, axiom,
% 1.27/1.46    (![A:$i]:
% 1.27/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.27/1.46       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.27/1.46  thf('5', plain,
% 1.27/1.46      (![X22 : $i]:
% 1.27/1.46         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 1.27/1.46          | ~ (l1_struct_0 @ X22)
% 1.27/1.46          | (v2_struct_0 @ X22))),
% 1.27/1.46      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.27/1.46  thf('6', plain,
% 1.27/1.46      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.27/1.46        | (v2_struct_0 @ sk_B)
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup-', [status(thm)], ['4', '5'])).
% 1.27/1.46  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('8', plain,
% 1.27/1.46      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['6', '7'])).
% 1.27/1.46  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('clc', [status(thm)], ['8', '9'])).
% 1.27/1.46  thf(d3_struct_0, axiom,
% 1.27/1.46    (![A:$i]:
% 1.27/1.46     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.27/1.46  thf('11', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('12', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf(d1_funct_2, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.27/1.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.27/1.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.27/1.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.27/1.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.27/1.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.27/1.46  thf(zf_stmt_1, axiom,
% 1.27/1.46    (![B:$i,A:$i]:
% 1.27/1.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.27/1.46       ( zip_tseitin_0 @ B @ A ) ))).
% 1.27/1.46  thf('13', plain,
% 1.27/1.46      (![X10 : $i, X11 : $i]:
% 1.27/1.46         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.27/1.46  thf('14', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.27/1.46  thf(zf_stmt_3, axiom,
% 1.27/1.46    (![C:$i,B:$i,A:$i]:
% 1.27/1.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.27/1.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.27/1.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.27/1.46  thf(zf_stmt_5, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.27/1.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.27/1.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.27/1.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.27/1.46  thf('15', plain,
% 1.27/1.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.46         (~ (zip_tseitin_0 @ X15 @ X16)
% 1.27/1.46          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 1.27/1.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.27/1.46  thf('16', plain,
% 1.27/1.46      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.27/1.46        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['14', '15'])).
% 1.27/1.46  thf('17', plain,
% 1.27/1.46      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.27/1.46        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['13', '16'])).
% 1.27/1.46  thf('18', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('19', plain,
% 1.27/1.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.27/1.46         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 1.27/1.46          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 1.27/1.46          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.27/1.46  thf('20', plain,
% 1.27/1.46      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.27/1.46        | ((u1_struct_0 @ sk_A)
% 1.27/1.46            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['18', '19'])).
% 1.27/1.46  thf('21', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(redefinition_k1_relset_1, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.27/1.46  thf('22', plain,
% 1.27/1.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.27/1.46         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 1.27/1.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.27/1.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.27/1.46  thf('23', plain,
% 1.27/1.46      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k1_relat_1 @ sk_C))),
% 1.27/1.46      inference('sup-', [status(thm)], ['21', '22'])).
% 1.27/1.46  thf('24', plain,
% 1.27/1.46      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.27/1.46        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.27/1.46      inference('demod', [status(thm)], ['20', '23'])).
% 1.27/1.46  thf('25', plain,
% 1.27/1.46      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.27/1.46        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['17', '24'])).
% 1.27/1.46  thf('26', plain,
% 1.27/1.46      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B)
% 1.27/1.46        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.27/1.46      inference('sup+', [status(thm)], ['12', '25'])).
% 1.27/1.46  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('29', plain,
% 1.27/1.46      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.27/1.46        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.27/1.46      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.27/1.46  thf('30', plain,
% 1.27/1.46      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_A)
% 1.27/1.46        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.27/1.46      inference('sup+', [status(thm)], ['11', '29'])).
% 1.27/1.46  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('32', plain,
% 1.27/1.46      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.27/1.46        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.27/1.46      inference('demod', [status(thm)], ['30', '31'])).
% 1.27/1.46  thf(t55_funct_1, axiom,
% 1.27/1.46    (![A:$i]:
% 1.27/1.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.27/1.46       ( ( v2_funct_1 @ A ) =>
% 1.27/1.46         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.27/1.46           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.27/1.46  thf('33', plain,
% 1.27/1.46      (![X0 : $i]:
% 1.27/1.46         (~ (v2_funct_1 @ X0)
% 1.27/1.46          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.27/1.46          | ~ (v1_funct_1 @ X0)
% 1.27/1.46          | ~ (v1_relat_1 @ X0))),
% 1.27/1.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.27/1.46  thf('34', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('35', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('36', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('37', plain,
% 1.27/1.46      (((m1_subset_1 @ sk_C @ 
% 1.27/1.46         (k1_zfmisc_1 @ 
% 1.27/1.46          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_A))),
% 1.27/1.46      inference('sup+', [status(thm)], ['35', '36'])).
% 1.27/1.46  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('39', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['37', '38'])).
% 1.27/1.46  thf('40', plain,
% 1.27/1.46      (((m1_subset_1 @ sk_C @ 
% 1.27/1.46         (k1_zfmisc_1 @ 
% 1.27/1.46          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['34', '39'])).
% 1.27/1.46  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('42', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['40', '41'])).
% 1.27/1.46  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('44', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.27/1.46      inference('demod', [status(thm)], ['42', '43'])).
% 1.27/1.46  thf(d4_tops_2, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.27/1.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.46       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.27/1.46         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.27/1.46  thf('45', plain,
% 1.27/1.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.27/1.46         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 1.27/1.46          | ~ (v2_funct_1 @ X25)
% 1.27/1.46          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 1.27/1.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.27/1.46          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.27/1.46          | ~ (v1_funct_1 @ X25))),
% 1.27/1.46      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.27/1.46  thf('46', plain,
% 1.27/1.46      ((~ (v1_funct_1 @ sk_C)
% 1.27/1.46        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.27/1.46        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46            = (k2_funct_1 @ sk_C))
% 1.27/1.46        | ~ (v2_funct_1 @ sk_C)
% 1.27/1.46        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46            != (k2_relat_1 @ sk_C)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.27/1.46  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('48', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('49', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('50', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('51', plain,
% 1.27/1.46      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_A))),
% 1.27/1.46      inference('sup+', [status(thm)], ['49', '50'])).
% 1.27/1.46  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('53', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['51', '52'])).
% 1.27/1.46  thf('54', plain,
% 1.27/1.46      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['48', '53'])).
% 1.27/1.46  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('56', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['54', '55'])).
% 1.27/1.46  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('58', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('demod', [status(thm)], ['56', '57'])).
% 1.27/1.46  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('60', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('61', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('62', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('63', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46          = (k2_struct_0 @ sk_B))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_A))),
% 1.27/1.46      inference('sup+', [status(thm)], ['61', '62'])).
% 1.27/1.46  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('65', plain,
% 1.27/1.46      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['63', '64'])).
% 1.27/1.46  thf('66', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46          = (k2_struct_0 @ sk_B))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['60', '65'])).
% 1.27/1.46  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('68', plain,
% 1.27/1.46      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['66', '67'])).
% 1.27/1.46  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('71', plain,
% 1.27/1.46      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46         = (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.27/1.46  thf('72', plain,
% 1.27/1.46      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46          = (k2_funct_1 @ sk_C))
% 1.27/1.46        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.27/1.46      inference('demod', [status(thm)], ['46', '47', '58', '59', '71'])).
% 1.27/1.46  thf('73', plain,
% 1.27/1.46      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46         = (k2_funct_1 @ sk_C))),
% 1.27/1.46      inference('simplify', [status(thm)], ['72'])).
% 1.27/1.46  thf('74', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('75', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('76', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('77', plain,
% 1.27/1.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_B))
% 1.27/1.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46            != (k2_struct_0 @ sk_A)))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('78', plain,
% 1.27/1.46      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('split', [status(esa)], ['77'])).
% 1.27/1.46  thf('79', plain,
% 1.27/1.46      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46           != (k2_struct_0 @ sk_A))
% 1.27/1.46         | ~ (l1_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['76', '78'])).
% 1.27/1.46  thf('80', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('81', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('demod', [status(thm)], ['79', '80'])).
% 1.27/1.46  thf('82', plain,
% 1.27/1.46      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46           != (k2_struct_0 @ sk_A))
% 1.27/1.46         | ~ (l1_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['75', '81'])).
% 1.27/1.46  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('84', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('demod', [status(thm)], ['82', '83'])).
% 1.27/1.46  thf('85', plain,
% 1.27/1.46      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46           != (k2_struct_0 @ sk_A))
% 1.27/1.46         | ~ (l1_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['74', '84'])).
% 1.27/1.46  thf('86', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('87', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('demod', [status(thm)], ['85', '86'])).
% 1.27/1.46  thf('88', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('90', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.27/1.46  thf('91', plain,
% 1.27/1.46      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['73', '90'])).
% 1.27/1.46  thf('92', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('93', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('94', plain,
% 1.27/1.46      (((m1_subset_1 @ sk_C @ 
% 1.27/1.46         (k1_zfmisc_1 @ 
% 1.27/1.46          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['92', '93'])).
% 1.27/1.46  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('96', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['94', '95'])).
% 1.27/1.46  thf('97', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('98', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.27/1.46      inference('demod', [status(thm)], ['96', '97'])).
% 1.27/1.46  thf(t31_funct_2, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.27/1.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.46       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.27/1.46         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.27/1.46           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.27/1.46           ( m1_subset_1 @
% 1.27/1.46             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.27/1.46  thf('99', plain,
% 1.27/1.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.27/1.46         (~ (v2_funct_1 @ X18)
% 1.27/1.46          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 1.27/1.46          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 1.27/1.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.27/1.46          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 1.27/1.46          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 1.27/1.46          | ~ (v1_funct_1 @ X18))),
% 1.27/1.46      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.27/1.46  thf('100', plain,
% 1.27/1.46      ((~ (v1_funct_1 @ sk_C)
% 1.27/1.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.27/1.46        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.27/1.46           (k1_zfmisc_1 @ 
% 1.27/1.46            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.27/1.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46            != (k2_relat_1 @ sk_C))
% 1.27/1.46        | ~ (v2_funct_1 @ sk_C))),
% 1.27/1.46      inference('sup-', [status(thm)], ['98', '99'])).
% 1.27/1.46  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('102', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('103', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('104', plain,
% 1.27/1.46      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['102', '103'])).
% 1.27/1.46  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('106', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['104', '105'])).
% 1.27/1.46  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('108', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('demod', [status(thm)], ['106', '107'])).
% 1.27/1.46  thf('109', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('110', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('111', plain,
% 1.27/1.46      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46          = (k2_struct_0 @ sk_B))
% 1.27/1.46        | ~ (l1_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['109', '110'])).
% 1.27/1.46  thf('112', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('113', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.27/1.46         = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['111', '112'])).
% 1.27/1.46  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('116', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46         = (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.27/1.46  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('118', plain,
% 1.27/1.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.27/1.46         (k1_zfmisc_1 @ 
% 1.27/1.46          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.27/1.46        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.27/1.46      inference('demod', [status(thm)], ['100', '101', '108', '116', '117'])).
% 1.27/1.46  thf('119', plain,
% 1.27/1.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.27/1.46      inference('simplify', [status(thm)], ['118'])).
% 1.27/1.46  thf('120', plain,
% 1.27/1.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.27/1.46         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 1.27/1.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.27/1.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.27/1.46  thf('121', plain,
% 1.27/1.46      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['119', '120'])).
% 1.27/1.46  thf('122', plain,
% 1.27/1.46      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_A))))),
% 1.27/1.46      inference('demod', [status(thm)], ['91', '121'])).
% 1.27/1.46  thf('123', plain,
% 1.27/1.46      (![X0 : $i]:
% 1.27/1.46         (~ (v2_funct_1 @ X0)
% 1.27/1.46          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.27/1.46          | ~ (v1_funct_1 @ X0)
% 1.27/1.46          | ~ (v1_relat_1 @ X0))),
% 1.27/1.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.27/1.46  thf('124', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.27/1.46      inference('demod', [status(thm)], ['96', '97'])).
% 1.27/1.46  thf('125', plain,
% 1.27/1.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.27/1.46         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 1.27/1.46          | ~ (v2_funct_1 @ X25)
% 1.27/1.46          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 1.27/1.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.27/1.46          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.27/1.46          | ~ (v1_funct_1 @ X25))),
% 1.27/1.46      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.27/1.46  thf('126', plain,
% 1.27/1.46      ((~ (v1_funct_1 @ sk_C)
% 1.27/1.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.27/1.46        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46            = (k2_funct_1 @ sk_C))
% 1.27/1.46        | ~ (v2_funct_1 @ sk_C)
% 1.27/1.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46            != (k2_relat_1 @ sk_C)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['124', '125'])).
% 1.27/1.46  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('128', plain,
% 1.27/1.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('demod', [status(thm)], ['106', '107'])).
% 1.27/1.46  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('130', plain,
% 1.27/1.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46         = (k2_relat_1 @ sk_C))),
% 1.27/1.46      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.27/1.46  thf('131', plain,
% 1.27/1.46      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46          = (k2_funct_1 @ sk_C))
% 1.27/1.46        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.27/1.46      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 1.27/1.46  thf('132', plain,
% 1.27/1.46      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.27/1.46         = (k2_funct_1 @ sk_C))),
% 1.27/1.46      inference('simplify', [status(thm)], ['131'])).
% 1.27/1.46  thf('133', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('134', plain,
% 1.27/1.46      (![X21 : $i]:
% 1.27/1.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.27/1.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.27/1.46  thf('135', plain,
% 1.27/1.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('split', [status(esa)], ['77'])).
% 1.27/1.46  thf('136', plain,
% 1.27/1.46      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46           != (k2_struct_0 @ sk_B))
% 1.27/1.46         | ~ (l1_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['134', '135'])).
% 1.27/1.46  thf('137', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('138', plain,
% 1.27/1.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['136', '137'])).
% 1.27/1.46  thf('139', plain,
% 1.27/1.46      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46           != (k2_struct_0 @ sk_B))
% 1.27/1.46         | ~ (l1_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['133', '138'])).
% 1.27/1.46  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('141', plain,
% 1.27/1.46      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          != (k2_struct_0 @ sk_B)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['139', '140'])).
% 1.27/1.46  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('144', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.27/1.46      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.46  thf('145', plain,
% 1.27/1.46      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.27/1.46          != (k2_relat_1 @ sk_C)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 1.27/1.46  thf('146', plain,
% 1.27/1.46      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['132', '145'])).
% 1.27/1.46  thf('147', plain,
% 1.27/1.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.27/1.46      inference('simplify', [status(thm)], ['118'])).
% 1.27/1.46  thf('148', plain,
% 1.27/1.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.27/1.46         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 1.27/1.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.27/1.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.27/1.46  thf('149', plain,
% 1.27/1.46      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['147', '148'])).
% 1.27/1.46  thf('150', plain,
% 1.27/1.46      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['146', '149'])).
% 1.27/1.46  thf('151', plain,
% 1.27/1.46      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.27/1.46         | ~ (v1_relat_1 @ sk_C)
% 1.27/1.46         | ~ (v1_funct_1 @ sk_C)
% 1.27/1.46         | ~ (v2_funct_1 @ sk_C)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('sup-', [status(thm)], ['123', '150'])).
% 1.27/1.46  thf('152', plain,
% 1.27/1.46      ((m1_subset_1 @ sk_C @ 
% 1.27/1.46        (k1_zfmisc_1 @ 
% 1.27/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(cc1_relset_1, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.46       ( v1_relat_1 @ C ) ))).
% 1.27/1.46  thf('153', plain,
% 1.27/1.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.27/1.46         ((v1_relat_1 @ X1)
% 1.27/1.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 1.27/1.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.27/1.46  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.46      inference('sup-', [status(thm)], ['152', '153'])).
% 1.27/1.46  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('157', plain,
% 1.27/1.46      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.27/1.46         <= (~
% 1.27/1.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46                = (k2_struct_0 @ sk_B))))),
% 1.27/1.46      inference('demod', [status(thm)], ['151', '154', '155', '156'])).
% 1.27/1.46  thf('158', plain,
% 1.27/1.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          = (k2_struct_0 @ sk_B)))),
% 1.27/1.46      inference('simplify', [status(thm)], ['157'])).
% 1.27/1.46  thf('159', plain,
% 1.27/1.46      (~
% 1.27/1.46       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          = (k2_struct_0 @ sk_A))) | 
% 1.27/1.46       ~
% 1.27/1.46       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          = (k2_struct_0 @ sk_B)))),
% 1.27/1.46      inference('split', [status(esa)], ['77'])).
% 1.27/1.46  thf('160', plain,
% 1.27/1.46      (~
% 1.27/1.46       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.27/1.46          = (k2_struct_0 @ sk_A)))),
% 1.27/1.46      inference('sat_resolution*', [status(thm)], ['158', '159'])).
% 1.27/1.46  thf('161', plain,
% 1.27/1.46      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 1.27/1.46      inference('simpl_trail', [status(thm)], ['122', '160'])).
% 1.27/1.46  thf('162', plain,
% 1.27/1.46      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 1.27/1.46        | ~ (v1_relat_1 @ sk_C)
% 1.27/1.46        | ~ (v1_funct_1 @ sk_C)
% 1.27/1.46        | ~ (v2_funct_1 @ sk_C))),
% 1.27/1.46      inference('sup-', [status(thm)], ['33', '161'])).
% 1.27/1.46  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.46      inference('sup-', [status(thm)], ['152', '153'])).
% 1.27/1.46  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('166', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 1.27/1.46      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 1.27/1.46  thf('167', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.27/1.46      inference('simplify_reflect-', [status(thm)], ['32', '166'])).
% 1.27/1.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.27/1.46  thf('168', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.27/1.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.27/1.46  thf('169', plain, ($false),
% 1.27/1.46      inference('demod', [status(thm)], ['10', '167', '168'])).
% 1.27/1.46  
% 1.27/1.46  % SZS output end Refutation
% 1.27/1.46  
% 1.27/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
