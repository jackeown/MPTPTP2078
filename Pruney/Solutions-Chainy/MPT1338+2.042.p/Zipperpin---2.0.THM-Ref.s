%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sCSYAmU0tL

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:54 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 685 expanded)
%              Number of leaves         :   44 ( 220 expanded)
%              Depth                    :   15
%              Number of atoms          : 1900 (17089 expanded)
%              Number of equality atoms :  150 ( 960 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41','48','57','58','66'])).

thf('68',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('70',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('73',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_relset_1 @ X15 @ X16 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('76',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('92',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','25','26','31','70','89','94'])).

thf('96',plain,
    ( $false
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('98',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('99',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('101',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('109',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('112',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('120',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['134','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('148',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['147','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('158',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133','144','145','146','158'])).

thf('160',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('162',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119','160','161'])).

thf('163',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','162'])).

thf('164',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('166',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['164','165'])).

thf('167',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['96','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sCSYAmU0tL
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:31:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.53/1.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.76  % Solved by: fo/fo7.sh
% 1.53/1.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.76  % done 447 iterations in 1.293s
% 1.53/1.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.76  % SZS output start Refutation
% 1.53/1.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.53/1.76  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.53/1.76  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.53/1.76  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.76  thf(sk_C_type, type, sk_C: $i).
% 1.53/1.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.53/1.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.53/1.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.53/1.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.53/1.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.53/1.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.53/1.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.53/1.76  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.53/1.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.53/1.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.53/1.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.53/1.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.53/1.76  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.53/1.76  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.53/1.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.53/1.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.53/1.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.53/1.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.53/1.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.53/1.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.53/1.76  thf(d3_struct_0, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.53/1.76  thf('0', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf(t62_tops_2, conjecture,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( l1_struct_0 @ A ) =>
% 1.53/1.76       ( ![B:$i]:
% 1.53/1.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.53/1.76           ( ![C:$i]:
% 1.53/1.76             ( ( ( v1_funct_1 @ C ) & 
% 1.53/1.76                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.53/1.76                 ( m1_subset_1 @
% 1.53/1.76                   C @ 
% 1.53/1.76                   ( k1_zfmisc_1 @
% 1.53/1.76                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.53/1.76               ( ( ( ( k2_relset_1 @
% 1.53/1.76                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.53/1.76                     ( k2_struct_0 @ B ) ) & 
% 1.53/1.76                   ( v2_funct_1 @ C ) ) =>
% 1.53/1.76                 ( ( ( k1_relset_1 @
% 1.53/1.76                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.53/1.76                       ( k2_tops_2 @
% 1.53/1.76                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.53/1.76                     ( k2_struct_0 @ B ) ) & 
% 1.53/1.76                   ( ( k2_relset_1 @
% 1.53/1.76                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.53/1.76                       ( k2_tops_2 @
% 1.53/1.76                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.53/1.76                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.53/1.76  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.76    (~( ![A:$i]:
% 1.53/1.76        ( ( l1_struct_0 @ A ) =>
% 1.53/1.76          ( ![B:$i]:
% 1.53/1.76            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.53/1.76              ( ![C:$i]:
% 1.53/1.76                ( ( ( v1_funct_1 @ C ) & 
% 1.53/1.76                    ( v1_funct_2 @
% 1.53/1.76                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.53/1.76                    ( m1_subset_1 @
% 1.53/1.76                      C @ 
% 1.53/1.76                      ( k1_zfmisc_1 @
% 1.53/1.76                        ( k2_zfmisc_1 @
% 1.53/1.76                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.53/1.76                  ( ( ( ( k2_relset_1 @
% 1.53/1.76                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.53/1.76                        ( k2_struct_0 @ B ) ) & 
% 1.53/1.76                      ( v2_funct_1 @ C ) ) =>
% 1.53/1.76                    ( ( ( k1_relset_1 @
% 1.53/1.76                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.53/1.76                          ( k2_tops_2 @
% 1.53/1.76                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.53/1.76                        ( k2_struct_0 @ B ) ) & 
% 1.53/1.76                      ( ( k2_relset_1 @
% 1.53/1.76                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.53/1.76                          ( k2_tops_2 @
% 1.53/1.76                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.53/1.76                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.53/1.76    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.53/1.76  thf('1', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_B))
% 1.53/1.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76            != (k2_struct_0 @ sk_A)))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('2', plain,
% 1.53/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_A)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_A))))),
% 1.53/1.76      inference('split', [status(esa)], ['1'])).
% 1.53/1.76  thf('3', plain,
% 1.53/1.76      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76           != (k2_struct_0 @ sk_A))
% 1.53/1.76         | ~ (l1_struct_0 @ sk_B)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_A))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['0', '2'])).
% 1.53/1.76  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('5', plain,
% 1.53/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_A)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_A))))),
% 1.53/1.76      inference('demod', [status(thm)], ['3', '4'])).
% 1.53/1.76  thf(d1_funct_2, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.53/1.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.53/1.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.53/1.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.53/1.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.53/1.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.53/1.76  thf(zf_stmt_1, axiom,
% 1.53/1.76    (![B:$i,A:$i]:
% 1.53/1.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.53/1.76       ( zip_tseitin_0 @ B @ A ) ))).
% 1.53/1.76  thf('6', plain,
% 1.53/1.76      (![X17 : $i, X18 : $i]:
% 1.53/1.76         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.76  thf('7', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.53/1.76  thf(zf_stmt_3, axiom,
% 1.53/1.76    (![C:$i,B:$i,A:$i]:
% 1.53/1.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.53/1.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.53/1.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.53/1.76  thf(zf_stmt_5, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.53/1.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.53/1.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.53/1.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.53/1.76  thf('8', plain,
% 1.53/1.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.53/1.76         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.53/1.76          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.53/1.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.53/1.76  thf('9', plain,
% 1.53/1.76      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.53/1.76        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['7', '8'])).
% 1.53/1.76  thf('10', plain,
% 1.53/1.76      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.53/1.76        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['6', '9'])).
% 1.53/1.76  thf('11', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('12', plain,
% 1.53/1.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.53/1.76         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.53/1.76          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.53/1.76          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.53/1.76  thf('13', plain,
% 1.53/1.76      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.53/1.76        | ((u1_struct_0 @ sk_A)
% 1.53/1.76            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['11', '12'])).
% 1.53/1.76  thf('14', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(redefinition_k1_relset_1, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.53/1.76  thf('15', plain,
% 1.53/1.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.53/1.76         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.53/1.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.53/1.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.53/1.76  thf('16', plain,
% 1.53/1.76      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('sup-', [status(thm)], ['14', '15'])).
% 1.53/1.76  thf('17', plain,
% 1.53/1.76      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.53/1.76        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)], ['13', '16'])).
% 1.53/1.76  thf('18', plain,
% 1.53/1.76      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.53/1.76        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['10', '17'])).
% 1.53/1.76  thf(fc2_struct_0, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.53/1.76       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.53/1.76  thf('19', plain,
% 1.53/1.76      (![X26 : $i]:
% 1.53/1.76         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 1.53/1.76          | ~ (l1_struct_0 @ X26)
% 1.53/1.76          | (v2_struct_0 @ X26))),
% 1.53/1.76      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.53/1.76  thf('20', plain,
% 1.53/1.76      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.53/1.76        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.53/1.76        | (v2_struct_0 @ sk_B)
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup-', [status(thm)], ['18', '19'])).
% 1.53/1.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.53/1.76  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.53/1.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.53/1.76  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('23', plain,
% 1.53/1.76      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.53/1.76  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('25', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('clc', [status(thm)], ['23', '24'])).
% 1.53/1.76  thf('26', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('clc', [status(thm)], ['23', '24'])).
% 1.53/1.76  thf('27', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(redefinition_k2_relset_1, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.53/1.76  thf('28', plain,
% 1.53/1.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.76         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.53/1.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.53/1.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.53/1.76  thf('29', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_relat_1 @ sk_C))),
% 1.53/1.76      inference('sup-', [status(thm)], ['27', '28'])).
% 1.53/1.76  thf('30', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('32', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('33', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('34', plain,
% 1.53/1.76      (((m1_subset_1 @ sk_C @ 
% 1.53/1.76         (k1_zfmisc_1 @ 
% 1.53/1.76          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['32', '33'])).
% 1.53/1.76  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('36', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('demod', [status(thm)], ['34', '35'])).
% 1.53/1.76  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('38', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.53/1.76      inference('demod', [status(thm)], ['36', '37'])).
% 1.53/1.76  thf(d4_tops_2, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.53/1.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.53/1.76       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.53/1.76         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.53/1.76  thf('39', plain,
% 1.53/1.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.53/1.76         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.53/1.76          | ~ (v2_funct_1 @ X29)
% 1.53/1.76          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.53/1.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.53/1.76          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.53/1.76          | ~ (v1_funct_1 @ X29))),
% 1.53/1.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.53/1.76  thf('40', plain,
% 1.53/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.53/1.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.53/1.76        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76            = (k2_funct_1 @ sk_C))
% 1.53/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.53/1.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76            != (k2_relat_1 @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['38', '39'])).
% 1.53/1.76  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('42', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('43', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('44', plain,
% 1.53/1.76      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['42', '43'])).
% 1.53/1.76  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('46', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['44', '45'])).
% 1.53/1.76  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('48', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['46', '47'])).
% 1.53/1.76  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(d9_funct_1, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.53/1.76       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.53/1.76  thf('50', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (~ (v2_funct_1 @ X0)
% 1.53/1.76          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 1.53/1.76          | ~ (v1_funct_1 @ X0)
% 1.53/1.76          | ~ (v1_relat_1 @ X0))),
% 1.53/1.76      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.53/1.76  thf('51', plain,
% 1.53/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.53/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.53/1.76        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['49', '50'])).
% 1.53/1.76  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('53', plain,
% 1.53/1.76      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)], ['51', '52'])).
% 1.53/1.76  thf('54', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(cc1_relset_1, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( v1_relat_1 @ C ) ))).
% 1.53/1.76  thf('55', plain,
% 1.53/1.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.53/1.76         ((v1_relat_1 @ X2)
% 1.53/1.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.53/1.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.53/1.76  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 1.53/1.76      inference('sup-', [status(thm)], ['54', '55'])).
% 1.53/1.76  thf('57', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['53', '56'])).
% 1.53/1.76  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('59', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('60', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('61', plain,
% 1.53/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76          = (k2_struct_0 @ sk_B))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['59', '60'])).
% 1.53/1.76  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('63', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['61', '62'])).
% 1.53/1.76  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('66', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76         = (k2_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.53/1.76  thf('67', plain,
% 1.53/1.76      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76          = (k4_relat_1 @ sk_C))
% 1.53/1.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)], ['40', '41', '48', '57', '58', '66'])).
% 1.53/1.76  thf('68', plain,
% 1.53/1.76      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76         = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('simplify', [status(thm)], ['67'])).
% 1.53/1.76  thf('69', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('clc', [status(thm)], ['23', '24'])).
% 1.53/1.76  thf('70', plain,
% 1.53/1.76      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76         = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['68', '69'])).
% 1.53/1.76  thf('71', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(dt_k3_relset_1, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( m1_subset_1 @
% 1.53/1.76         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.53/1.76         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.53/1.76  thf('72', plain,
% 1.53/1.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.53/1.76         ((m1_subset_1 @ (k3_relset_1 @ X5 @ X6 @ X7) @ 
% 1.53/1.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 1.53/1.76          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.53/1.76      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.53/1.76  thf('73', plain,
% 1.53/1.76      ((m1_subset_1 @ 
% 1.53/1.76        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['71', '72'])).
% 1.53/1.76  thf('74', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(redefinition_k3_relset_1, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.76       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.53/1.76  thf('75', plain,
% 1.53/1.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.53/1.76         (((k3_relset_1 @ X15 @ X16 @ X14) = (k4_relat_1 @ X14))
% 1.53/1.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.53/1.76      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.53/1.76  thf('76', plain,
% 1.53/1.76      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('sup-', [status(thm)], ['74', '75'])).
% 1.53/1.76  thf('77', plain,
% 1.53/1.76      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.53/1.76      inference('demod', [status(thm)], ['73', '76'])).
% 1.53/1.76  thf('78', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('clc', [status(thm)], ['23', '24'])).
% 1.53/1.76  thf('79', plain,
% 1.53/1.76      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.53/1.76      inference('demod', [status(thm)], ['77', '78'])).
% 1.53/1.76  thf('80', plain,
% 1.53/1.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.76         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.53/1.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.53/1.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.53/1.76  thf('81', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.53/1.76         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['79', '80'])).
% 1.53/1.76  thf('82', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['53', '56'])).
% 1.53/1.76  thf(t55_funct_1, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.53/1.76       ( ( v2_funct_1 @ A ) =>
% 1.53/1.76         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.53/1.76           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.53/1.76  thf('83', plain,
% 1.53/1.76      (![X1 : $i]:
% 1.53/1.76         (~ (v2_funct_1 @ X1)
% 1.53/1.76          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.53/1.76          | ~ (v1_funct_1 @ X1)
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.53/1.76  thf('84', plain,
% 1.53/1.76      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.53/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.53/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.53/1.76        | ~ (v2_funct_1 @ sk_C))),
% 1.53/1.76      inference('sup+', [status(thm)], ['82', '83'])).
% 1.53/1.76  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 1.53/1.76      inference('sup-', [status(thm)], ['54', '55'])).
% 1.53/1.76  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('88', plain,
% 1.53/1.76      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 1.53/1.76  thf('89', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.53/1.76         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['81', '88'])).
% 1.53/1.76  thf('90', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('91', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('clc', [status(thm)], ['23', '24'])).
% 1.53/1.76  thf('92', plain,
% 1.53/1.76      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['90', '91'])).
% 1.53/1.76  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('94', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['92', '93'])).
% 1.53/1.76  thf('95', plain,
% 1.53/1.76      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_A))))),
% 1.53/1.76      inference('demod', [status(thm)],
% 1.53/1.76                ['5', '25', '26', '31', '70', '89', '94'])).
% 1.53/1.76  thf('96', plain,
% 1.53/1.76      (($false)
% 1.53/1.76         <= (~
% 1.53/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_A))))),
% 1.53/1.76      inference('simplify', [status(thm)], ['95'])).
% 1.53/1.76  thf('97', plain,
% 1.53/1.76      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.53/1.76      inference('demod', [status(thm)], ['77', '78'])).
% 1.53/1.76  thf('98', plain,
% 1.53/1.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.53/1.76         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.53/1.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.53/1.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.53/1.76  thf('99', plain,
% 1.53/1.76      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.53/1.76         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['97', '98'])).
% 1.53/1.76  thf('100', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['53', '56'])).
% 1.53/1.76  thf('101', plain,
% 1.53/1.76      (![X1 : $i]:
% 1.53/1.76         (~ (v2_funct_1 @ X1)
% 1.53/1.76          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.53/1.76          | ~ (v1_funct_1 @ X1)
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.53/1.76  thf('102', plain,
% 1.53/1.76      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.53/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.53/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.53/1.76        | ~ (v2_funct_1 @ sk_C))),
% 1.53/1.76      inference('sup+', [status(thm)], ['100', '101'])).
% 1.53/1.76  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 1.53/1.76      inference('sup-', [status(thm)], ['54', '55'])).
% 1.53/1.76  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('106', plain,
% 1.53/1.76      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 1.53/1.76  thf('107', plain,
% 1.53/1.76      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.53/1.76         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['99', '106'])).
% 1.53/1.76  thf('108', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.53/1.76      inference('clc', [status(thm)], ['23', '24'])).
% 1.53/1.76  thf('109', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('110', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('111', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_B)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('split', [status(esa)], ['1'])).
% 1.53/1.76  thf('112', plain,
% 1.53/1.76      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76           != (k2_struct_0 @ sk_B))
% 1.53/1.76         | ~ (l1_struct_0 @ sk_A)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['110', '111'])).
% 1.53/1.76  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('114', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_B)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('demod', [status(thm)], ['112', '113'])).
% 1.53/1.76  thf('115', plain,
% 1.53/1.76      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76           != (k2_struct_0 @ sk_B))
% 1.53/1.76         | ~ (l1_struct_0 @ sk_B)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['109', '114'])).
% 1.53/1.76  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('117', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_B)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('demod', [status(thm)], ['115', '116'])).
% 1.53/1.76  thf('118', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.53/1.76          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          != (k2_struct_0 @ sk_B)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['108', '117'])).
% 1.53/1.76  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('120', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('121', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('122', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('123', plain,
% 1.53/1.76      (((m1_subset_1 @ sk_C @ 
% 1.53/1.76         (k1_zfmisc_1 @ 
% 1.53/1.76          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['121', '122'])).
% 1.53/1.76  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('125', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.53/1.76      inference('demod', [status(thm)], ['123', '124'])).
% 1.53/1.76  thf('126', plain,
% 1.53/1.76      (((m1_subset_1 @ sk_C @ 
% 1.53/1.76         (k1_zfmisc_1 @ 
% 1.53/1.76          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['120', '125'])).
% 1.53/1.76  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('128', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('demod', [status(thm)], ['126', '127'])).
% 1.53/1.76  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('130', plain,
% 1.53/1.76      ((m1_subset_1 @ sk_C @ 
% 1.53/1.76        (k1_zfmisc_1 @ 
% 1.53/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.53/1.76      inference('demod', [status(thm)], ['128', '129'])).
% 1.53/1.76  thf('131', plain,
% 1.53/1.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.53/1.76         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.53/1.76          | ~ (v2_funct_1 @ X29)
% 1.53/1.76          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.53/1.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.53/1.76          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.53/1.76          | ~ (v1_funct_1 @ X29))),
% 1.53/1.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.53/1.76  thf('132', plain,
% 1.53/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.53/1.76        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.53/1.76        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76            = (k2_funct_1 @ sk_C))
% 1.53/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.53/1.76        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76            != (k2_relat_1 @ sk_C)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['130', '131'])).
% 1.53/1.76  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('134', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('135', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('136', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('137', plain,
% 1.53/1.76      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['135', '136'])).
% 1.53/1.76  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('139', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['137', '138'])).
% 1.53/1.76  thf('140', plain,
% 1.53/1.76      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['134', '139'])).
% 1.53/1.76  thf('141', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('142', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['140', '141'])).
% 1.53/1.76  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('144', plain,
% 1.53/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['142', '143'])).
% 1.53/1.76  thf('145', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['53', '56'])).
% 1.53/1.76  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('147', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('148', plain,
% 1.53/1.76      (![X25 : $i]:
% 1.53/1.76         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.53/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.76  thf('149', plain,
% 1.53/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('150', plain,
% 1.53/1.76      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76          = (k2_struct_0 @ sk_B))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['148', '149'])).
% 1.53/1.76  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('152', plain,
% 1.53/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['150', '151'])).
% 1.53/1.76  thf('153', plain,
% 1.53/1.76      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76          = (k2_struct_0 @ sk_B))
% 1.53/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['147', '152'])).
% 1.53/1.76  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('155', plain,
% 1.53/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.53/1.76         = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('demod', [status(thm)], ['153', '154'])).
% 1.53/1.76  thf('156', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('157', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('158', plain,
% 1.53/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76         = (k2_relat_1 @ sk_C))),
% 1.53/1.76      inference('demod', [status(thm)], ['155', '156', '157'])).
% 1.53/1.76  thf('159', plain,
% 1.53/1.76      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76          = (k4_relat_1 @ sk_C))
% 1.53/1.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)],
% 1.53/1.76                ['132', '133', '144', '145', '146', '158'])).
% 1.53/1.76  thf('160', plain,
% 1.53/1.76      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.53/1.76         = (k4_relat_1 @ sk_C))),
% 1.53/1.76      inference('simplify', [status(thm)], ['159'])).
% 1.53/1.76  thf('161', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '30'])).
% 1.53/1.76  thf('162', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.53/1.76          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('demod', [status(thm)], ['118', '119', '160', '161'])).
% 1.53/1.76  thf('163', plain,
% 1.53/1.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.53/1.76         <= (~
% 1.53/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76                = (k2_struct_0 @ sk_B))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['107', '162'])).
% 1.53/1.76  thf('164', plain,
% 1.53/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          = (k2_struct_0 @ sk_B)))),
% 1.53/1.76      inference('simplify', [status(thm)], ['163'])).
% 1.53/1.76  thf('165', plain,
% 1.53/1.76      (~
% 1.53/1.76       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          = (k2_struct_0 @ sk_A))) | 
% 1.53/1.76       ~
% 1.53/1.76       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          = (k2_struct_0 @ sk_B)))),
% 1.53/1.76      inference('split', [status(esa)], ['1'])).
% 1.53/1.76  thf('166', plain,
% 1.53/1.76      (~
% 1.53/1.76       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.53/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.53/1.76          = (k2_struct_0 @ sk_A)))),
% 1.53/1.76      inference('sat_resolution*', [status(thm)], ['164', '165'])).
% 1.53/1.76  thf('167', plain, ($false),
% 1.53/1.76      inference('simpl_trail', [status(thm)], ['96', '166'])).
% 1.53/1.76  
% 1.53/1.76  % SZS output end Refutation
% 1.53/1.76  
% 1.53/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
