%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hxPegt495C

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:55 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 572 expanded)
%              Number of leaves         :   40 ( 182 expanded)
%              Depth                    :   18
%              Number of atoms          : 2023 (15441 expanded)
%              Number of equality atoms :  154 ( 865 expanded)
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,negated_conjecture,(
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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

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

thf('40',plain,(
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

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','53','54','66'])).

thf('68',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('85',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','85'])).

thf('87',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

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

thf('94',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('108',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('111',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','103','111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('120',plain,(
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

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('124',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('125',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('126',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['72'])).

thf('131',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('136',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('140',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('143',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('144',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','144'])).

thf('146',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('148',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('152',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','149','150','151'])).

thf('153',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['72'])).

thf('155',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['153','154'])).

thf('156',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['117','155'])).

thf('157',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['147','148'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('161',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hxPegt495C
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 342 iterations in 0.693s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.14  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.91/1.14  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.91/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.91/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.14  thf(d3_struct_0, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.91/1.14  thf('0', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf(d1_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_0, axiom,
% 0.91/1.14    (![B:$i,A:$i]:
% 0.91/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      (![X10 : $i, X11 : $i]:
% 0.91/1.14         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(t62_tops_2, conjecture,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( l1_struct_0 @ A ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.91/1.14           ( ![C:$i]:
% 0.91/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.14                 ( m1_subset_1 @
% 0.91/1.14                   C @ 
% 0.91/1.14                   ( k1_zfmisc_1 @
% 0.91/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.14               ( ( ( ( k2_relset_1 @
% 0.91/1.14                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.14                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.14                   ( v2_funct_1 @ C ) ) =>
% 0.91/1.14                 ( ( ( k1_relset_1 @
% 0.91/1.14                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.14                       ( k2_tops_2 @
% 0.91/1.14                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.14                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.14                   ( ( k2_relset_1 @
% 0.91/1.14                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.14                       ( k2_tops_2 @
% 0.91/1.14                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.14                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_1, negated_conjecture,
% 0.91/1.14    (~( ![A:$i]:
% 0.91/1.14        ( ( l1_struct_0 @ A ) =>
% 0.91/1.14          ( ![B:$i]:
% 0.91/1.14            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.91/1.14              ( ![C:$i]:
% 0.91/1.14                ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.14                    ( v1_funct_2 @
% 0.91/1.14                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.14                    ( m1_subset_1 @
% 0.91/1.14                      C @ 
% 0.91/1.14                      ( k1_zfmisc_1 @
% 0.91/1.14                        ( k2_zfmisc_1 @
% 0.91/1.14                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.14                  ( ( ( ( k2_relset_1 @
% 0.91/1.14                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.14                        ( k2_struct_0 @ B ) ) & 
% 0.91/1.14                      ( v2_funct_1 @ C ) ) =>
% 0.91/1.14                    ( ( ( k1_relset_1 @
% 0.91/1.14                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.14                          ( k2_tops_2 @
% 0.91/1.14                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.14                        ( k2_struct_0 @ B ) ) & 
% 0.91/1.14                      ( ( k2_relset_1 @
% 0.91/1.14                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.14                          ( k2_tops_2 @
% 0.91/1.14                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.14                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.91/1.14  thf('2', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.14  thf(zf_stmt_3, axiom,
% 0.91/1.14    (![C:$i,B:$i,A:$i]:
% 0.91/1.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.14  thf(zf_stmt_5, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.14  thf('3', plain,
% 0.91/1.14      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.91/1.14         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.91/1.14          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.91/1.14          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.14  thf('4', plain,
% 0.91/1.14      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.14        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.91/1.14        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['1', '4'])).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.14         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.91/1.14          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.91/1.14          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.14        | ((u1_struct_0 @ sk_A)
% 0.91/1.14            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.14  thf('10', plain,
% 0.91/1.14      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.91/1.14          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k1_relat_1 @ sk_C))),
% 0.91/1.14      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.91/1.14      inference('demod', [status(thm)], ['8', '11'])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.91/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['5', '12'])).
% 0.91/1.14  thf(fc2_struct_0, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.14       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      (![X22 : $i]:
% 0.91/1.14         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.91/1.14          | ~ (l1_struct_0 @ X22)
% 0.91/1.14          | (v2_struct_0 @ X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.91/1.14        | (v2_struct_0 @ sk_B)
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup-', [status(thm)], ['13', '14'])).
% 0.91/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.14  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.14  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.91/1.14  thf('19', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('20', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.91/1.14      inference('clc', [status(thm)], ['18', '19'])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.14      inference('sup+', [status(thm)], ['0', '20'])).
% 0.91/1.14  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('23', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.14  thf(t55_funct_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.14       ( ( v2_funct_1 @ A ) =>
% 0.91/1.14         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.91/1.14           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X0)
% 0.91/1.14          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.91/1.14  thf('25', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('26', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('28', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_C @ 
% 0.91/1.14         (k1_zfmisc_1 @ 
% 0.91/1.14          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.14      inference('sup+', [status(thm)], ['26', '27'])).
% 0.91/1.14  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['28', '29'])).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_C @ 
% 0.91/1.14         (k1_zfmisc_1 @ 
% 0.91/1.14          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['25', '30'])).
% 0.91/1.14  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['31', '32'])).
% 0.91/1.14  thf('34', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.14         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.91/1.14          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.14  thf('36', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('39', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.91/1.14      inference('demod', [status(thm)], ['33', '38'])).
% 0.91/1.14  thf(d4_tops_2, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.14       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.91/1.14         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.91/1.14  thf('40', plain,
% 0.91/1.14      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.14         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.91/1.14          | ~ (v2_funct_1 @ X25)
% 0.91/1.14          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.91/1.14          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.91/1.14          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.91/1.14          | ~ (v1_funct_1 @ X25))),
% 0.91/1.14      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.91/1.14  thf('41', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.91/1.14        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14            = (k2_funct_1 @ sk_C))
% 0.91/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.14        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14            != (k2_relat_1 @ sk_C)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('43', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('44', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('45', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('46', plain,
% 0.91/1.14      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.14      inference('sup+', [status(thm)], ['44', '45'])).
% 0.91/1.14  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['46', '47'])).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['43', '48'])).
% 0.91/1.14  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('51', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['49', '50'])).
% 0.91/1.14  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('53', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['51', '52'])).
% 0.91/1.14  thf('54', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('55', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('57', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('58', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.14      inference('sup+', [status(thm)], ['56', '57'])).
% 0.91/1.14  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('60', plain,
% 0.91/1.14      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['58', '59'])).
% 0.91/1.14  thf('61', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['55', '60'])).
% 0.91/1.14  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('63', plain,
% 0.91/1.14      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.91/1.14  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('66', plain,
% 0.91/1.14      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14         = (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.91/1.14  thf('67', plain,
% 0.91/1.14      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14          = (k2_funct_1 @ sk_C))
% 0.91/1.14        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.91/1.14      inference('demod', [status(thm)], ['41', '42', '53', '54', '66'])).
% 0.91/1.14  thf('68', plain,
% 0.91/1.14      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14         = (k2_funct_1 @ sk_C))),
% 0.91/1.14      inference('simplify', [status(thm)], ['67'])).
% 0.91/1.14  thf('69', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('70', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('71', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_B))
% 0.91/1.14        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14            != (k2_struct_0 @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('73', plain,
% 0.91/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('split', [status(esa)], ['72'])).
% 0.91/1.14  thf('74', plain,
% 0.91/1.14      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14           != (k2_struct_0 @ sk_A))
% 0.91/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['71', '73'])).
% 0.91/1.14  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('76', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['74', '75'])).
% 0.91/1.14  thf('77', plain,
% 0.91/1.14      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14           != (k2_struct_0 @ sk_A))
% 0.91/1.14         | ~ (l1_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['70', '76'])).
% 0.91/1.14  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('79', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['77', '78'])).
% 0.91/1.14  thf('80', plain,
% 0.91/1.14      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14           != (k2_struct_0 @ sk_A))
% 0.91/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['69', '79'])).
% 0.91/1.14  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('82', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['80', '81'])).
% 0.91/1.14  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.91/1.14  thf('86', plain,
% 0.91/1.14      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['68', '85'])).
% 0.91/1.14  thf('87', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('88', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('89', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_C @ 
% 0.91/1.14         (k1_zfmisc_1 @ 
% 0.91/1.14          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['87', '88'])).
% 0.91/1.14  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('91', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['89', '90'])).
% 0.91/1.14  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('93', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.91/1.14      inference('demod', [status(thm)], ['91', '92'])).
% 0.91/1.14  thf(t31_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.14       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.91/1.14         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.91/1.14           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.91/1.14           ( m1_subset_1 @
% 0.91/1.14             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.91/1.14  thf('94', plain,
% 0.91/1.14      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X18)
% 0.91/1.14          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.91/1.14          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.91/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.91/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.91/1.14          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.91/1.14          | ~ (v1_funct_1 @ X18))),
% 0.91/1.14      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.91/1.14  thf('95', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.91/1.14        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.14           (k1_zfmisc_1 @ 
% 0.91/1.14            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.91/1.14        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14            != (k2_relat_1 @ sk_C))
% 0.91/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.91/1.14      inference('sup-', [status(thm)], ['93', '94'])).
% 0.91/1.14  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('97', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('98', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('99', plain,
% 0.91/1.14      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.14  thf('100', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('101', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['99', '100'])).
% 0.91/1.14  thf('102', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('103', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['101', '102'])).
% 0.91/1.14  thf('104', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('105', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('106', plain,
% 0.91/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B))
% 0.91/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['104', '105'])).
% 0.91/1.14  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('108', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14         = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['106', '107'])).
% 0.91/1.14  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('111', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14         = (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.91/1.14  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('113', plain,
% 0.91/1.14      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.14         (k1_zfmisc_1 @ 
% 0.91/1.14          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.91/1.14        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.91/1.14      inference('demod', [status(thm)], ['95', '96', '103', '111', '112'])).
% 0.91/1.14  thf('114', plain,
% 0.91/1.14      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('simplify', [status(thm)], ['113'])).
% 0.91/1.14  thf('115', plain,
% 0.91/1.14      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.14         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.91/1.14          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.14  thf('116', plain,
% 0.91/1.14      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['114', '115'])).
% 0.91/1.14  thf('117', plain,
% 0.91/1.14      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['86', '116'])).
% 0.91/1.14  thf('118', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X0)
% 0.91/1.14          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v1_relat_1 @ X0))),
% 0.91/1.14      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.91/1.14  thf('119', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.91/1.14      inference('demod', [status(thm)], ['91', '92'])).
% 0.91/1.14  thf('120', plain,
% 0.91/1.14      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.14         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.91/1.14          | ~ (v2_funct_1 @ X25)
% 0.91/1.14          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.91/1.14          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.91/1.14          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.91/1.14          | ~ (v1_funct_1 @ X25))),
% 0.91/1.14      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.91/1.14  thf('121', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.91/1.14        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14            = (k2_funct_1 @ sk_C))
% 0.91/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.14        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14            != (k2_relat_1 @ sk_C)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['119', '120'])).
% 0.91/1.14  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('123', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['101', '102'])).
% 0.91/1.14  thf('124', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('125', plain,
% 0.91/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14         = (k2_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.91/1.14  thf('126', plain,
% 0.91/1.14      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14          = (k2_funct_1 @ sk_C))
% 0.91/1.14        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.91/1.14      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 0.91/1.14  thf('127', plain,
% 0.91/1.14      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.14         = (k2_funct_1 @ sk_C))),
% 0.91/1.14      inference('simplify', [status(thm)], ['126'])).
% 0.91/1.14  thf('128', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('129', plain,
% 0.91/1.14      (![X21 : $i]:
% 0.91/1.14         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.14  thf('130', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('split', [status(esa)], ['72'])).
% 0.91/1.14  thf('131', plain,
% 0.91/1.14      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14           != (k2_struct_0 @ sk_B))
% 0.91/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['129', '130'])).
% 0.91/1.14  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('133', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['131', '132'])).
% 0.91/1.14  thf('134', plain,
% 0.91/1.14      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14           != (k2_struct_0 @ sk_B))
% 0.91/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['128', '133'])).
% 0.91/1.14  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('136', plain,
% 0.91/1.14      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          != (k2_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['134', '135'])).
% 0.91/1.14  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('138', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('139', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('140', plain,
% 0.91/1.14      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.91/1.14          != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 0.91/1.14  thf('141', plain,
% 0.91/1.14      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['127', '140'])).
% 0.91/1.14  thf('142', plain,
% 0.91/1.14      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('simplify', [status(thm)], ['113'])).
% 0.91/1.14  thf('143', plain,
% 0.91/1.14      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.91/1.14          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.14  thf('144', plain,
% 0.91/1.14      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['142', '143'])).
% 0.91/1.14  thf('145', plain,
% 0.91/1.14      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['141', '144'])).
% 0.91/1.14  thf('146', plain,
% 0.91/1.14      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.91/1.14         | ~ (v1_relat_1 @ sk_C)
% 0.91/1.14         | ~ (v1_funct_1 @ sk_C)
% 0.91/1.14         | ~ (v2_funct_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['118', '145'])).
% 0.91/1.14  thf('147', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf(cc1_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( v1_relat_1 @ C ) ))).
% 0.91/1.14  thf('148', plain,
% 0.91/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.14         ((v1_relat_1 @ X1)
% 0.91/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.14  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.14      inference('sup-', [status(thm)], ['147', '148'])).
% 0.91/1.14  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('152', plain,
% 0.91/1.14      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['146', '149', '150', '151'])).
% 0.91/1.14  thf('153', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_B)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['152'])).
% 0.91/1.14  thf('154', plain,
% 0.91/1.14      (~
% 0.91/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_A))) | 
% 0.91/1.14       ~
% 0.91/1.14       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_B)))),
% 0.91/1.14      inference('split', [status(esa)], ['72'])).
% 0.91/1.14  thf('155', plain,
% 0.91/1.14      (~
% 0.91/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_A)))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)], ['153', '154'])).
% 0.91/1.14  thf('156', plain,
% 0.91/1.14      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['117', '155'])).
% 0.91/1.14  thf('157', plain,
% 0.91/1.14      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.91/1.14        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.91/1.14      inference('sup-', [status(thm)], ['24', '156'])).
% 0.91/1.14  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.14      inference('sup-', [status(thm)], ['147', '148'])).
% 0.91/1.14  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('161', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.91/1.14  thf('162', plain, ($false),
% 0.91/1.14      inference('simplify_reflect-', [status(thm)], ['23', '161'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.91/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
