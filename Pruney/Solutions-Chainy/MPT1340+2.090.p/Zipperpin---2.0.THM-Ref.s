%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0OSwVduDoU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:22 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 866 expanded)
%              Number of leaves         :   49 ( 275 expanded)
%              Depth                    :   23
%              Number of atoms          : 2013 (18499 expanded)
%              Number of equality atoms :  109 ( 598 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

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

thf('3',plain,(
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('38',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','36','37'])).

thf('39',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('48',plain,(
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

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','59','60','69'])).

thf('71',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['38','71'])).

thf('73',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('78',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('82',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
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

thf('87',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('89',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('98',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('107',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('108',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('109',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('111',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('118',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('123',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','119','120','121','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('132',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','132'])).

thf('134',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['117','118'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('142',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','96','105','140','143'])).

thf('145',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','144'])).

thf('146',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['117','118'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['75','151'])).

thf('153',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['117','118'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('160',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','164'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('168',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['157','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0OSwVduDoU
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 2.20/2.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.20/2.39  % Solved by: fo/fo7.sh
% 2.20/2.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.20/2.39  % done 684 iterations in 1.894s
% 2.20/2.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.20/2.39  % SZS output start Refutation
% 2.20/2.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.20/2.39  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.20/2.39  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.20/2.39  thf(sk_B_type, type, sk_B: $i).
% 2.20/2.39  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.20/2.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.20/2.39  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.20/2.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.20/2.39  thf(sk_A_type, type, sk_A: $i).
% 2.20/2.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.20/2.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.20/2.39  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.20/2.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.20/2.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.20/2.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.20/2.39  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.20/2.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.20/2.39  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.20/2.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.20/2.39  thf(sk_C_type, type, sk_C: $i).
% 2.20/2.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.20/2.39  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.20/2.39  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.20/2.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.20/2.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.20/2.39  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.20/2.39  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.20/2.39  thf(t65_funct_1, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.20/2.39       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 2.20/2.39  thf('0', plain,
% 2.20/2.39      (![X10 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X10)
% 2.20/2.39          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 2.20/2.39          | ~ (v1_funct_1 @ X10)
% 2.20/2.39          | ~ (v1_relat_1 @ X10))),
% 2.20/2.39      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.20/2.39  thf(d3_struct_0, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.20/2.39  thf('1', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('2', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('3', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf(t64_tops_2, conjecture,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( l1_struct_0 @ A ) =>
% 2.20/2.39       ( ![B:$i]:
% 2.20/2.39         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.20/2.39           ( ![C:$i]:
% 2.20/2.39             ( ( ( v1_funct_1 @ C ) & 
% 2.20/2.39                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.20/2.39                 ( m1_subset_1 @
% 2.20/2.39                   C @ 
% 2.20/2.39                   ( k1_zfmisc_1 @
% 2.20/2.39                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.20/2.39               ( ( ( ( k2_relset_1 @
% 2.20/2.39                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.20/2.39                     ( k2_struct_0 @ B ) ) & 
% 2.20/2.39                   ( v2_funct_1 @ C ) ) =>
% 2.20/2.39                 ( r2_funct_2 @
% 2.20/2.39                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 2.20/2.39                   ( k2_tops_2 @
% 2.20/2.39                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.20/2.39                     ( k2_tops_2 @
% 2.20/2.39                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 2.20/2.39                   C ) ) ) ) ) ) ))).
% 2.20/2.39  thf(zf_stmt_0, negated_conjecture,
% 2.20/2.39    (~( ![A:$i]:
% 2.20/2.39        ( ( l1_struct_0 @ A ) =>
% 2.20/2.39          ( ![B:$i]:
% 2.20/2.39            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.20/2.39              ( ![C:$i]:
% 2.20/2.39                ( ( ( v1_funct_1 @ C ) & 
% 2.20/2.39                    ( v1_funct_2 @
% 2.20/2.39                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.20/2.39                    ( m1_subset_1 @
% 2.20/2.39                      C @ 
% 2.20/2.39                      ( k1_zfmisc_1 @
% 2.20/2.39                        ( k2_zfmisc_1 @
% 2.20/2.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.20/2.39                  ( ( ( ( k2_relset_1 @
% 2.20/2.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.20/2.39                        ( k2_struct_0 @ B ) ) & 
% 2.20/2.39                      ( v2_funct_1 @ C ) ) =>
% 2.20/2.39                    ( r2_funct_2 @
% 2.20/2.39                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 2.20/2.39                      ( k2_tops_2 @
% 2.20/2.39                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.20/2.39                        ( k2_tops_2 @
% 2.20/2.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 2.20/2.39                      C ) ) ) ) ) ) ) )),
% 2.20/2.39    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 2.20/2.39  thf('4', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.20/2.39           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('5', plain,
% 2.20/2.39      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 2.20/2.39           sk_C)
% 2.20/2.39        | ~ (l1_struct_0 @ sk_A))),
% 2.20/2.39      inference('sup-', [status(thm)], ['3', '4'])).
% 2.20/2.39  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('7', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.20/2.39           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['5', '6'])).
% 2.20/2.39  thf('8', plain,
% 2.20/2.39      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.20/2.39           sk_C)
% 2.20/2.39        | ~ (l1_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup-', [status(thm)], ['2', '7'])).
% 2.20/2.39  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('10', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.20/2.39           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['8', '9'])).
% 2.20/2.39  thf(d1_funct_2, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i]:
% 2.20/2.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.20/2.39       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.20/2.39           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.20/2.39             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.20/2.39         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.20/2.39           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.20/2.39             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.20/2.39  thf(zf_stmt_1, axiom,
% 2.20/2.39    (![B:$i,A:$i]:
% 2.20/2.39     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.20/2.39       ( zip_tseitin_0 @ B @ A ) ))).
% 2.20/2.39  thf('11', plain,
% 2.20/2.39      (![X17 : $i, X18 : $i]:
% 2.20/2.39         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.20/2.39  thf('12', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.20/2.39  thf(zf_stmt_3, axiom,
% 2.20/2.39    (![C:$i,B:$i,A:$i]:
% 2.20/2.39     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.20/2.39       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.20/2.39  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.20/2.39  thf(zf_stmt_5, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i]:
% 2.20/2.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.20/2.39       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.20/2.39         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.20/2.39           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.20/2.39             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.20/2.39  thf('13', plain,
% 2.20/2.39      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.20/2.39         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.20/2.39          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.20/2.39          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.20/2.39  thf('14', plain,
% 2.20/2.39      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.20/2.39        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['12', '13'])).
% 2.20/2.39  thf('15', plain,
% 2.20/2.39      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.20/2.39        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['11', '14'])).
% 2.20/2.39  thf('16', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('17', plain,
% 2.20/2.39      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.20/2.39         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.20/2.39          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.20/2.39          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.20/2.39  thf('18', plain,
% 2.20/2.39      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.20/2.39        | ((u1_struct_0 @ sk_A)
% 2.20/2.39            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['16', '17'])).
% 2.20/2.39  thf('19', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf(redefinition_k1_relset_1, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i]:
% 2.20/2.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.20/2.39       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.20/2.39  thf('20', plain,
% 2.20/2.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.20/2.39         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 2.20/2.39          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.20/2.39      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.20/2.39  thf('21', plain,
% 2.20/2.39      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k1_relat_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['19', '20'])).
% 2.20/2.39  thf('22', plain,
% 2.20/2.39      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.20/2.39        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 2.20/2.39      inference('demod', [status(thm)], ['18', '21'])).
% 2.20/2.39  thf('23', plain,
% 2.20/2.39      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.20/2.39        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['15', '22'])).
% 2.20/2.39  thf(fc2_struct_0, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.20/2.39       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.20/2.39  thf('24', plain,
% 2.20/2.39      (![X33 : $i]:
% 2.20/2.39         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 2.20/2.39          | ~ (l1_struct_0 @ X33)
% 2.20/2.39          | (v2_struct_0 @ X33))),
% 2.20/2.39      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.20/2.39  thf('25', plain,
% 2.20/2.39      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.20/2.39        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 2.20/2.39        | (v2_struct_0 @ sk_B)
% 2.20/2.39        | ~ (l1_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup-', [status(thm)], ['23', '24'])).
% 2.20/2.39  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.20/2.39  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.20/2.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.20/2.39  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('28', plain,
% 2.20/2.39      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.20/2.39  thf('29', plain, (~ (v2_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('30', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 2.20/2.39      inference('clc', [status(thm)], ['28', '29'])).
% 2.20/2.39  thf('31', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('32', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 2.20/2.39      inference('clc', [status(thm)], ['28', '29'])).
% 2.20/2.39  thf('33', plain,
% 2.20/2.39      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 2.20/2.39      inference('sup+', [status(thm)], ['31', '32'])).
% 2.20/2.39  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('35', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 2.20/2.39      inference('demod', [status(thm)], ['33', '34'])).
% 2.20/2.39  thf('36', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.20/2.39      inference('demod', [status(thm)], ['30', '35'])).
% 2.20/2.39  thf('37', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.20/2.39      inference('demod', [status(thm)], ['30', '35'])).
% 2.20/2.39  thf('38', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['10', '36', '37'])).
% 2.20/2.39  thf('39', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('40', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('41', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('42', plain,
% 2.20/2.39      (((m1_subset_1 @ sk_C @ 
% 2.20/2.39         (k1_zfmisc_1 @ 
% 2.20/2.39          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 2.20/2.39        | ~ (l1_struct_0 @ sk_A))),
% 2.20/2.39      inference('sup+', [status(thm)], ['40', '41'])).
% 2.20/2.39  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('44', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['42', '43'])).
% 2.20/2.39  thf('45', plain,
% 2.20/2.39      (((m1_subset_1 @ sk_C @ 
% 2.20/2.39         (k1_zfmisc_1 @ 
% 2.20/2.39          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.20/2.39        | ~ (l1_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup+', [status(thm)], ['39', '44'])).
% 2.20/2.39  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('47', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['45', '46'])).
% 2.20/2.39  thf(d4_tops_2, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i]:
% 2.20/2.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.20/2.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.20/2.39       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.20/2.39         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.20/2.39  thf('48', plain,
% 2.20/2.39      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.20/2.39         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 2.20/2.39          | ~ (v2_funct_1 @ X36)
% 2.20/2.39          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 2.20/2.39          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.20/2.39          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.20/2.39          | ~ (v1_funct_1 @ X36))),
% 2.20/2.39      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.20/2.39  thf('49', plain,
% 2.20/2.39      ((~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.20/2.39        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39            = (k2_funct_1 @ sk_C))
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C)
% 2.20/2.39        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39            != (k2_struct_0 @ sk_B)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['47', '48'])).
% 2.20/2.39  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('51', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('52', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('53', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('54', plain,
% 2.20/2.39      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.20/2.39        | ~ (l1_struct_0 @ sk_A))),
% 2.20/2.39      inference('sup+', [status(thm)], ['52', '53'])).
% 2.20/2.39  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('56', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['54', '55'])).
% 2.20/2.39  thf('57', plain,
% 2.20/2.39      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.20/2.39        | ~ (l1_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup+', [status(thm)], ['51', '56'])).
% 2.20/2.39  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('59', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['57', '58'])).
% 2.20/2.39  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('61', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('62', plain,
% 2.20/2.39      (![X32 : $i]:
% 2.20/2.39         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 2.20/2.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.20/2.39  thf('63', plain,
% 2.20/2.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('64', plain,
% 2.20/2.39      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39          = (k2_struct_0 @ sk_B))
% 2.20/2.39        | ~ (l1_struct_0 @ sk_A))),
% 2.20/2.39      inference('sup+', [status(thm)], ['62', '63'])).
% 2.20/2.39  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('66', plain,
% 2.20/2.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['64', '65'])).
% 2.20/2.39  thf('67', plain,
% 2.20/2.39      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39          = (k2_struct_0 @ sk_B))
% 2.20/2.39        | ~ (l1_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup+', [status(thm)], ['61', '66'])).
% 2.20/2.39  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('69', plain,
% 2.20/2.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['67', '68'])).
% 2.20/2.39  thf('70', plain,
% 2.20/2.39      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39          = (k2_funct_1 @ sk_C))
% 2.20/2.39        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 2.20/2.39      inference('demod', [status(thm)], ['49', '50', '59', '60', '69'])).
% 2.20/2.39  thf('71', plain,
% 2.20/2.39      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_funct_1 @ sk_C))),
% 2.20/2.39      inference('simplify', [status(thm)], ['70'])).
% 2.20/2.39  thf('72', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39           (k2_funct_1 @ sk_C)) @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['38', '71'])).
% 2.20/2.39  thf('73', plain,
% 2.20/2.39      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_funct_1 @ sk_C)) @ 
% 2.20/2.39           sk_C)
% 2.20/2.39        | ~ (l1_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup-', [status(thm)], ['1', '72'])).
% 2.20/2.39  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('75', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39           (k2_funct_1 @ sk_C)) @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['73', '74'])).
% 2.20/2.39  thf(t55_funct_1, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.20/2.39       ( ( v2_funct_1 @ A ) =>
% 2.20/2.39         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.20/2.39           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.20/2.39  thf('76', plain,
% 2.20/2.39      (![X8 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X8)
% 2.20/2.39          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 2.20/2.39          | ~ (v1_funct_1 @ X8)
% 2.20/2.39          | ~ (v1_relat_1 @ X8))),
% 2.20/2.39      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.20/2.39  thf('77', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['45', '46'])).
% 2.20/2.39  thf(t31_funct_2, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i]:
% 2.20/2.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.20/2.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.20/2.39       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.20/2.39         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.20/2.39           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.20/2.39           ( m1_subset_1 @
% 2.20/2.39             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.20/2.39  thf('78', plain,
% 2.20/2.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X29)
% 2.20/2.39          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 2.20/2.39          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 2.20/2.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.20/2.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.20/2.39          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 2.20/2.39          | ~ (v1_funct_1 @ X29))),
% 2.20/2.39      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.20/2.39  thf('79', plain,
% 2.20/2.39      ((~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.20/2.39        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.20/2.39           (k1_zfmisc_1 @ 
% 2.20/2.39            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 2.20/2.39        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39            != (k2_struct_0 @ sk_B))
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['77', '78'])).
% 2.20/2.39  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('81', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['57', '58'])).
% 2.20/2.39  thf('82', plain,
% 2.20/2.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['67', '68'])).
% 2.20/2.39  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('84', plain,
% 2.20/2.39      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.20/2.39         (k1_zfmisc_1 @ 
% 2.20/2.39          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 2.20/2.39        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 2.20/2.39      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 2.20/2.39  thf('85', plain,
% 2.20/2.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.20/2.39      inference('simplify', [status(thm)], ['84'])).
% 2.20/2.39  thf('86', plain,
% 2.20/2.39      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.20/2.39         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 2.20/2.39          | ~ (v2_funct_1 @ X36)
% 2.20/2.39          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 2.20/2.39          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.20/2.39          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.20/2.39          | ~ (v1_funct_1 @ X36))),
% 2.20/2.39      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.20/2.39  thf('87', plain,
% 2.20/2.39      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.20/2.39        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 2.20/2.39             (k2_struct_0 @ sk_A))
% 2.20/2.39        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.20/2.39        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.20/2.39        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['85', '86'])).
% 2.20/2.39  thf('88', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['45', '46'])).
% 2.20/2.39  thf('89', plain,
% 2.20/2.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X29)
% 2.20/2.39          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 2.20/2.39          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 2.20/2.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.20/2.39          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 2.20/2.39          | ~ (v1_funct_1 @ X29))),
% 2.20/2.39      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.20/2.39  thf('90', plain,
% 2.20/2.39      ((~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.20/2.39        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.20/2.39        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39            != (k2_struct_0 @ sk_B))
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['88', '89'])).
% 2.20/2.39  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('92', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['57', '58'])).
% 2.20/2.39  thf('93', plain,
% 2.20/2.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['67', '68'])).
% 2.20/2.39  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('95', plain,
% 2.20/2.39      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.20/2.39        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 2.20/2.39      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 2.20/2.39  thf('96', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.20/2.39      inference('simplify', [status(thm)], ['95'])).
% 2.20/2.39  thf('97', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['45', '46'])).
% 2.20/2.39  thf('98', plain,
% 2.20/2.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X29)
% 2.20/2.39          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 2.20/2.39          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 2.20/2.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.20/2.39          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 2.20/2.39          | ~ (v1_funct_1 @ X29))),
% 2.20/2.39      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.20/2.39  thf('99', plain,
% 2.20/2.39      ((~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.20/2.39        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 2.20/2.39           (k2_struct_0 @ sk_A))
% 2.20/2.39        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39            != (k2_struct_0 @ sk_B))
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['97', '98'])).
% 2.20/2.39  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('101', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['57', '58'])).
% 2.20/2.39  thf('102', plain,
% 2.20/2.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['67', '68'])).
% 2.20/2.39  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('104', plain,
% 2.20/2.39      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 2.20/2.39         (k2_struct_0 @ sk_A))
% 2.20/2.39        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 2.20/2.39      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 2.20/2.39  thf('105', plain,
% 2.20/2.39      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 2.20/2.39        (k2_struct_0 @ sk_A))),
% 2.20/2.39      inference('simplify', [status(thm)], ['104'])).
% 2.20/2.39  thf('106', plain,
% 2.20/2.39      (![X8 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X8)
% 2.20/2.39          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 2.20/2.39          | ~ (v1_funct_1 @ X8)
% 2.20/2.39          | ~ (v1_relat_1 @ X8))),
% 2.20/2.39      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.20/2.39  thf('107', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.20/2.39      inference('simplify', [status(thm)], ['95'])).
% 2.20/2.39  thf(t61_funct_1, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.20/2.39       ( ( v2_funct_1 @ A ) =>
% 2.20/2.39         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.20/2.39             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.20/2.39           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.20/2.39             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.20/2.39  thf('108', plain,
% 2.20/2.39      (![X9 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ X9)
% 2.20/2.39          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 2.20/2.39              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 2.20/2.39          | ~ (v1_funct_1 @ X9)
% 2.20/2.39          | ~ (v1_relat_1 @ X9))),
% 2.20/2.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.20/2.39  thf(t48_funct_1, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.20/2.39       ( ![B:$i]:
% 2.20/2.39         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.20/2.39           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 2.20/2.39               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 2.20/2.39             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 2.20/2.39  thf('109', plain,
% 2.20/2.39      (![X6 : $i, X7 : $i]:
% 2.20/2.39         (~ (v1_relat_1 @ X6)
% 2.20/2.39          | ~ (v1_funct_1 @ X6)
% 2.20/2.39          | (v2_funct_1 @ X7)
% 2.20/2.39          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 2.20/2.39          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 2.20/2.39          | ~ (v1_funct_1 @ X7)
% 2.20/2.39          | ~ (v1_relat_1 @ X7))),
% 2.20/2.39      inference('cnf', [status(esa)], [t48_funct_1])).
% 2.20/2.39  thf('110', plain,
% 2.20/2.39      (![X0 : $i]:
% 2.20/2.39         (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.20/2.39          | ~ (v1_relat_1 @ X0)
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | ~ (v2_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.20/2.39          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ X0))),
% 2.20/2.39      inference('sup-', [status(thm)], ['108', '109'])).
% 2.20/2.39  thf(fc4_funct_1, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.20/2.39       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.20/2.39  thf('111', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.20/2.39      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.20/2.39  thf('112', plain,
% 2.20/2.39      (![X0 : $i]:
% 2.20/2.39         (~ (v1_relat_1 @ X0)
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | ~ (v2_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.20/2.39          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ X0))),
% 2.20/2.39      inference('demod', [status(thm)], ['110', '111'])).
% 2.20/2.39  thf('113', plain,
% 2.20/2.39      (![X0 : $i]:
% 2.20/2.39         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.20/2.39          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.20/2.39          | ~ (v2_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ X0))),
% 2.20/2.39      inference('simplify', [status(thm)], ['112'])).
% 2.20/2.39  thf('114', plain,
% 2.20/2.39      ((~ (v1_relat_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.20/2.39        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.20/2.39        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['107', '113'])).
% 2.20/2.39  thf('115', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf(cc2_relat_1, axiom,
% 2.20/2.39    (![A:$i]:
% 2.20/2.39     ( ( v1_relat_1 @ A ) =>
% 2.20/2.39       ( ![B:$i]:
% 2.20/2.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.20/2.39  thf('116', plain,
% 2.20/2.39      (![X0 : $i, X1 : $i]:
% 2.20/2.39         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.20/2.39          | (v1_relat_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ X1))),
% 2.20/2.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.20/2.39  thf('117', plain,
% 2.20/2.39      ((~ (v1_relat_1 @ 
% 2.20/2.39           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 2.20/2.39        | (v1_relat_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['115', '116'])).
% 2.20/2.39  thf(fc6_relat_1, axiom,
% 2.20/2.39    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.20/2.39  thf('118', plain,
% 2.20/2.39      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.20/2.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.20/2.39  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['117', '118'])).
% 2.20/2.39  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('122', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf(redefinition_k2_relset_1, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i]:
% 2.20/2.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.20/2.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.20/2.39  thf('123', plain,
% 2.20/2.39      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.20/2.39         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.20/2.39          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.20/2.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.20/2.39  thf('124', plain,
% 2.20/2.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_relat_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['122', '123'])).
% 2.20/2.39  thf('125', plain,
% 2.20/2.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.20/2.39         = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('126', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup+', [status(thm)], ['124', '125'])).
% 2.20/2.39  thf('127', plain,
% 2.20/2.39      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.20/2.39        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.20/2.39        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('demod', [status(thm)], ['114', '119', '120', '121', '126'])).
% 2.20/2.39  thf('128', plain,
% 2.20/2.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.20/2.39      inference('simplify', [status(thm)], ['84'])).
% 2.20/2.39  thf('129', plain,
% 2.20/2.39      (![X0 : $i, X1 : $i]:
% 2.20/2.39         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.20/2.39          | (v1_relat_1 @ X0)
% 2.20/2.39          | ~ (v1_relat_1 @ X1))),
% 2.20/2.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.20/2.39  thf('130', plain,
% 2.20/2.39      ((~ (v1_relat_1 @ 
% 2.20/2.39           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 2.20/2.39        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['128', '129'])).
% 2.20/2.39  thf('131', plain,
% 2.20/2.39      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.20/2.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.20/2.39  thf('132', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.20/2.39      inference('demod', [status(thm)], ['130', '131'])).
% 2.20/2.39  thf('133', plain,
% 2.20/2.39      ((((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.20/2.39        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('demod', [status(thm)], ['127', '132'])).
% 2.20/2.39  thf('134', plain,
% 2.20/2.39      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 2.20/2.39        | ~ (v1_relat_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C)
% 2.20/2.39        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['106', '133'])).
% 2.20/2.39  thf('135', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.20/2.39      inference('sup+', [status(thm)], ['124', '125'])).
% 2.20/2.39  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['117', '118'])).
% 2.20/2.39  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('139', plain,
% 2.20/2.39      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 2.20/2.39        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 2.20/2.39  thf('140', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.20/2.39      inference('simplify', [status(thm)], ['139'])).
% 2.20/2.39  thf('141', plain,
% 2.20/2.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.20/2.39      inference('simplify', [status(thm)], ['84'])).
% 2.20/2.39  thf('142', plain,
% 2.20/2.39      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.20/2.39         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.20/2.39          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.20/2.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.20/2.39  thf('143', plain,
% 2.20/2.39      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['141', '142'])).
% 2.20/2.39  thf('144', plain,
% 2.20/2.39      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.20/2.39        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 2.20/2.39      inference('demod', [status(thm)], ['87', '96', '105', '140', '143'])).
% 2.20/2.39  thf('145', plain,
% 2.20/2.39      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 2.20/2.39        | ~ (v1_relat_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C)
% 2.20/2.39        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.20/2.39      inference('sup-', [status(thm)], ['76', '144'])).
% 2.20/2.39  thf('146', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 2.20/2.39      inference('demod', [status(thm)], ['33', '34'])).
% 2.20/2.39  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['117', '118'])).
% 2.20/2.39  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('150', plain,
% 2.20/2.39      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 2.20/2.39        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.20/2.39      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 2.20/2.39  thf('151', plain,
% 2.20/2.39      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.20/2.39         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.20/2.39      inference('simplify', [status(thm)], ['150'])).
% 2.20/2.39  thf('152', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.20/2.39          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['75', '151'])).
% 2.20/2.39  thf('153', plain,
% 2.20/2.39      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.20/2.39           sk_C)
% 2.20/2.39        | ~ (v1_relat_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v2_funct_1 @ sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['0', '152'])).
% 2.20/2.39  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['117', '118'])).
% 2.20/2.39  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('157', plain,
% 2.20/2.39      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.20/2.39          sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 2.20/2.39  thf('158', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['42', '43'])).
% 2.20/2.39  thf('159', plain,
% 2.20/2.39      ((m1_subset_1 @ sk_C @ 
% 2.20/2.39        (k1_zfmisc_1 @ 
% 2.20/2.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.20/2.39      inference('demod', [status(thm)], ['42', '43'])).
% 2.20/2.39  thf(reflexivity_r2_funct_2, axiom,
% 2.20/2.39    (![A:$i,B:$i,C:$i,D:$i]:
% 2.20/2.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.20/2.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.20/2.39         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.20/2.39         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.20/2.39       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 2.20/2.39  thf('160', plain,
% 2.20/2.39      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.20/2.39         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 2.20/2.39          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.20/2.39          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 2.20/2.39          | ~ (v1_funct_1 @ X27)
% 2.20/2.39          | ~ (v1_funct_1 @ X28)
% 2.20/2.39          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 2.20/2.39          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.20/2.39      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 2.20/2.39  thf('161', plain,
% 2.20/2.39      (![X0 : $i]:
% 2.20/2.39         (~ (m1_subset_1 @ X0 @ 
% 2.20/2.39             (k1_zfmisc_1 @ 
% 2.20/2.39              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 2.20/2.39          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | ~ (v1_funct_1 @ sk_C)
% 2.20/2.39          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.20/2.39          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.20/2.39             sk_C))),
% 2.20/2.39      inference('sup-', [status(thm)], ['159', '160'])).
% 2.20/2.39  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('163', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['54', '55'])).
% 2.20/2.39  thf('164', plain,
% 2.20/2.39      (![X0 : $i]:
% 2.20/2.39         (~ (m1_subset_1 @ X0 @ 
% 2.20/2.39             (k1_zfmisc_1 @ 
% 2.20/2.39              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 2.20/2.39          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.20/2.39          | ~ (v1_funct_1 @ X0)
% 2.20/2.39          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 2.20/2.39             sk_C))),
% 2.20/2.39      inference('demod', [status(thm)], ['161', '162', '163'])).
% 2.20/2.39  thf('165', plain,
% 2.20/2.39      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 2.20/2.39        | ~ (v1_funct_1 @ sk_C)
% 2.20/2.39        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 2.20/2.39      inference('sup-', [status(thm)], ['158', '164'])).
% 2.20/2.39  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 2.20/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.39  thf('167', plain,
% 2.20/2.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.20/2.39      inference('demod', [status(thm)], ['54', '55'])).
% 2.20/2.39  thf('168', plain,
% 2.20/2.39      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 2.20/2.39      inference('demod', [status(thm)], ['165', '166', '167'])).
% 2.20/2.39  thf('169', plain, ($false), inference('demod', [status(thm)], ['157', '168'])).
% 2.20/2.39  
% 2.20/2.39  % SZS output end Refutation
% 2.20/2.39  
% 2.20/2.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
