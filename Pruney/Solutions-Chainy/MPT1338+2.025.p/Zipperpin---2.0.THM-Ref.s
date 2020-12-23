%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E4busQvPOS

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:51 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 902 expanded)
%              Number of leaves         :   47 ( 283 expanded)
%              Depth                    :   21
%              Number of atoms          : 2114 (23239 expanded)
%              Number of equality atoms :  148 (1251 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','38'])).

thf('40',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

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

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','53','54','57'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','63'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('71',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('74',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','91','92','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('111',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','121'])).

thf('123',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','122'])).

thf('124',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','123'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('132',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['130','131'])).

thf('133',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['64','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('135',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('139',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('141',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

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

thf('142',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('145',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('146',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('148',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('151',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('152',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('157',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('158',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['154','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['149','167'])).

thf('169',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['146','168'])).

thf('170',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','169'])).

thf('171',plain,(
    ( u1_struct_0 @ sk_B )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','170'])).

thf('172',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','171'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('174',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    $false ),
    inference(simplify,[status(thm)],['175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E4busQvPOS
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.85/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.04  % Solved by: fo/fo7.sh
% 0.85/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.04  % done 445 iterations in 0.596s
% 0.85/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.04  % SZS output start Refutation
% 0.85/1.04  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.85/1.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.85/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.85/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.04  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.85/1.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.85/1.04  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.85/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.85/1.04  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.85/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.04  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.85/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.85/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.85/1.04  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.85/1.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.85/1.04  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.85/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.85/1.04  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.85/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.85/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.85/1.04  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.85/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.85/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.85/1.04  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.85/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.04  thf(d3_struct_0, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.85/1.04  thf('0', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf(t62_tops_2, conjecture,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( l1_struct_0 @ A ) =>
% 0.85/1.04       ( ![B:$i]:
% 0.85/1.04         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.85/1.04           ( ![C:$i]:
% 0.85/1.04             ( ( ( v1_funct_1 @ C ) & 
% 0.85/1.04                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.85/1.04                 ( m1_subset_1 @
% 0.85/1.04                   C @ 
% 0.85/1.04                   ( k1_zfmisc_1 @
% 0.85/1.04                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.85/1.04               ( ( ( ( k2_relset_1 @
% 0.85/1.04                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.85/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.85/1.04                   ( v2_funct_1 @ C ) ) =>
% 0.85/1.04                 ( ( ( k1_relset_1 @
% 0.85/1.04                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.85/1.04                       ( k2_tops_2 @
% 0.85/1.04                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.85/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.85/1.04                   ( ( k2_relset_1 @
% 0.85/1.04                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.85/1.04                       ( k2_tops_2 @
% 0.85/1.04                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.85/1.04                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.85/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.04    (~( ![A:$i]:
% 0.85/1.04        ( ( l1_struct_0 @ A ) =>
% 0.85/1.04          ( ![B:$i]:
% 0.85/1.04            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.85/1.04              ( ![C:$i]:
% 0.85/1.04                ( ( ( v1_funct_1 @ C ) & 
% 0.85/1.04                    ( v1_funct_2 @
% 0.85/1.04                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.85/1.04                    ( m1_subset_1 @
% 0.85/1.04                      C @ 
% 0.85/1.04                      ( k1_zfmisc_1 @
% 0.85/1.04                        ( k2_zfmisc_1 @
% 0.85/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.85/1.04                  ( ( ( ( k2_relset_1 @
% 0.85/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.85/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.85/1.04                      ( v2_funct_1 @ C ) ) =>
% 0.85/1.04                    ( ( ( k1_relset_1 @
% 0.85/1.04                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.85/1.04                          ( k2_tops_2 @
% 0.85/1.04                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.85/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.85/1.04                      ( ( k2_relset_1 @
% 0.85/1.04                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.85/1.04                          ( k2_tops_2 @
% 0.85/1.04                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.85/1.04                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.85/1.04    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.85/1.04  thf('1', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf(t132_funct_2, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( ( v1_funct_1 @ C ) & 
% 0.85/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.04       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.04           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.85/1.04           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.85/1.04  thf('2', plain,
% 0.85/1.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.85/1.04         (((X23) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_funct_1 @ X24)
% 0.85/1.04          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.85/1.04          | (v1_partfun1 @ X24 @ X25)
% 0.85/1.04          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.85/1.04          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.85/1.04          | ~ (v1_funct_1 @ X24))),
% 0.85/1.04      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.85/1.04  thf('3', plain,
% 0.85/1.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.85/1.04         (~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.85/1.04          | (v1_partfun1 @ X24 @ X25)
% 0.85/1.04          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.85/1.04          | ~ (v1_funct_1 @ X24)
% 0.85/1.04          | ((X23) = (k1_xboole_0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['2'])).
% 0.85/1.04  thf('4', plain,
% 0.85/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.85/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.85/1.04        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.85/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['1', '3'])).
% 0.85/1.04  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('6', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('7', plain,
% 0.85/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.85/1.04        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.85/1.04      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.85/1.04  thf(d4_partfun1, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.85/1.04       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.85/1.04  thf('8', plain,
% 0.85/1.04      (![X21 : $i, X22 : $i]:
% 0.85/1.04         (~ (v1_partfun1 @ X22 @ X21)
% 0.85/1.04          | ((k1_relat_1 @ X22) = (X21))
% 0.85/1.04          | ~ (v4_relat_1 @ X22 @ X21)
% 0.85/1.04          | ~ (v1_relat_1 @ X22))),
% 0.85/1.04      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.85/1.04  thf('9', plain,
% 0.85/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.85/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.85/1.04        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.85/1.04        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['7', '8'])).
% 0.85/1.04  thf('10', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf(cc1_relset_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.04       ( v1_relat_1 @ C ) ))).
% 0.85/1.04  thf('11', plain,
% 0.85/1.04      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.85/1.04         ((v1_relat_1 @ X4)
% 0.85/1.04          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.85/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.85/1.04  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.04      inference('sup-', [status(thm)], ['10', '11'])).
% 0.85/1.04  thf('13', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf(cc2_relset_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.04       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.85/1.04  thf('14', plain,
% 0.85/1.04      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.85/1.04         ((v4_relat_1 @ X7 @ X8)
% 0.85/1.04          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.85/1.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.85/1.04  thf('15', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.85/1.04      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.04  thf('16', plain,
% 0.85/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.85/1.04        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.85/1.04      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.85/1.04  thf(fc2_struct_0, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.85/1.04       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.85/1.04  thf('17', plain,
% 0.85/1.04      (![X27 : $i]:
% 0.85/1.04         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.85/1.04          | ~ (l1_struct_0 @ X27)
% 0.85/1.04          | (v2_struct_0 @ X27))),
% 0.85/1.04      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.85/1.04  thf('18', plain,
% 0.85/1.04      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.85/1.04        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.85/1.04        | (v2_struct_0 @ sk_B)
% 0.85/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.85/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.85/1.04  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.04  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('21', plain,
% 0.85/1.04      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.85/1.04  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('23', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.85/1.04      inference('clc', [status(thm)], ['21', '22'])).
% 0.85/1.04  thf('24', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('25', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.85/1.04      inference('clc', [status(thm)], ['21', '22'])).
% 0.85/1.04  thf('26', plain,
% 0.85/1.04      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.85/1.04      inference('sup+', [status(thm)], ['24', '25'])).
% 0.85/1.04  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('28', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.85/1.04      inference('demod', [status(thm)], ['26', '27'])).
% 0.85/1.04  thf('29', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.85/1.04      inference('demod', [status(thm)], ['23', '28'])).
% 0.85/1.04  thf('30', plain,
% 0.85/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04          != (k2_struct_0 @ sk_B))
% 0.85/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04            != (k2_struct_0 @ sk_A)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('31', plain,
% 0.85/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04          != (k2_struct_0 @ sk_B)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_B))))),
% 0.85/1.04      inference('split', [status(esa)], ['30'])).
% 0.85/1.04  thf('32', plain,
% 0.85/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04          != (k2_struct_0 @ sk_B)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_B))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['29', '31'])).
% 0.85/1.04  thf('33', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.85/1.04      inference('demod', [status(thm)], ['23', '28'])).
% 0.85/1.04  thf('34', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf(redefinition_k2_relset_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.85/1.04  thf('35', plain,
% 0.85/1.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.04         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.85/1.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.85/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.85/1.04  thf('36', plain,
% 0.85/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_relat_1 @ sk_C))),
% 0.85/1.04      inference('sup-', [status(thm)], ['34', '35'])).
% 0.85/1.04  thf('37', plain,
% 0.85/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf('39', plain,
% 0.85/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04          != (k2_relat_1 @ sk_C)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['32', '33', '38'])).
% 0.85/1.04  thf('40', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('41', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('42', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('43', plain,
% 0.85/1.04      (((m1_subset_1 @ sk_C @ 
% 0.85/1.04         (k1_zfmisc_1 @ 
% 0.85/1.04          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_A))),
% 0.85/1.04      inference('sup+', [status(thm)], ['41', '42'])).
% 0.85/1.04  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('45', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['43', '44'])).
% 0.85/1.04  thf(d4_tops_2, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.04       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.85/1.04         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.85/1.04  thf('46', plain,
% 0.85/1.04      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.85/1.04         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.85/1.04          | ~ (v2_funct_1 @ X30)
% 0.85/1.04          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.85/1.04          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.85/1.04          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.85/1.04          | ~ (v1_funct_1 @ X30))),
% 0.85/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.85/1.04  thf('47', plain,
% 0.85/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.85/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.85/1.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04            = (k2_funct_1 @ sk_C))
% 0.85/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.85/1.04        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04            != (u1_struct_0 @ sk_B)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['45', '46'])).
% 0.85/1.04  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('49', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('50', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('51', plain,
% 0.85/1.04      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_A))),
% 0.85/1.04      inference('sup+', [status(thm)], ['49', '50'])).
% 0.85/1.04  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('53', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('54', plain, ((v2_funct_1 @ sk_C)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('55', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['43', '44'])).
% 0.85/1.04  thf('56', plain,
% 0.85/1.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.04         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.85/1.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.85/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.85/1.04  thf('57', plain,
% 0.85/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_relat_1 @ sk_C))),
% 0.85/1.04      inference('sup-', [status(thm)], ['55', '56'])).
% 0.85/1.04  thf('58', plain,
% 0.85/1.04      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04          = (k2_funct_1 @ sk_C))
% 0.85/1.04        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.85/1.04      inference('demod', [status(thm)], ['47', '48', '53', '54', '57'])).
% 0.85/1.04  thf('59', plain,
% 0.85/1.04      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.85/1.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04            = (k2_funct_1 @ sk_C)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['40', '58'])).
% 0.85/1.04  thf('60', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('62', plain,
% 0.85/1.04      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.85/1.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04            = (k2_funct_1 @ sk_C)))),
% 0.85/1.04      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.85/1.04  thf('63', plain,
% 0.85/1.04      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_funct_1 @ sk_C))),
% 0.85/1.04      inference('simplify', [status(thm)], ['62'])).
% 0.85/1.04  thf('64', plain,
% 0.85/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['39', '63'])).
% 0.85/1.04  thf(t55_funct_1, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.85/1.04       ( ( v2_funct_1 @ A ) =>
% 0.85/1.04         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.85/1.04           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.85/1.04  thf('65', plain,
% 0.85/1.04      (![X3 : $i]:
% 0.85/1.04         (~ (v2_funct_1 @ X3)
% 0.85/1.04          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 0.85/1.04          | ~ (v1_funct_1 @ X3)
% 0.85/1.04          | ~ (v1_relat_1 @ X3))),
% 0.85/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.85/1.04  thf('66', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['43', '44'])).
% 0.85/1.04  thf(dt_k2_tops_2, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.04       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.85/1.04         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.85/1.04         ( m1_subset_1 @
% 0.85/1.04           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.85/1.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.85/1.04  thf('67', plain,
% 0.85/1.04      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.85/1.04         ((m1_subset_1 @ (k2_tops_2 @ X31 @ X32 @ X33) @ 
% 0.85/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.85/1.04          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.85/1.04          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.85/1.04          | ~ (v1_funct_1 @ X33))),
% 0.85/1.04      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.85/1.04  thf('68', plain,
% 0.85/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.85/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.85/1.04        | (m1_subset_1 @ 
% 0.85/1.04           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.85/1.04           (k1_zfmisc_1 @ 
% 0.85/1.04            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['66', '67'])).
% 0.85/1.04  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('70', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('71', plain,
% 0.85/1.04      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_funct_1 @ sk_C))),
% 0.85/1.04      inference('simplify', [status(thm)], ['62'])).
% 0.85/1.04  thf('72', plain,
% 0.85/1.04      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.85/1.04      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.85/1.04  thf('73', plain,
% 0.85/1.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.04         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.85/1.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.85/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.85/1.04  thf('74', plain,
% 0.85/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.04         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.85/1.04  thf('75', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('76', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['43', '44'])).
% 0.85/1.04  thf('77', plain,
% 0.85/1.04      (((m1_subset_1 @ sk_C @ 
% 0.85/1.04         (k1_zfmisc_1 @ 
% 0.85/1.04          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['75', '76'])).
% 0.85/1.04  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('79', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.85/1.04      inference('demod', [status(thm)], ['77', '78'])).
% 0.85/1.04  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf('81', plain,
% 0.85/1.04      ((m1_subset_1 @ sk_C @ 
% 0.85/1.04        (k1_zfmisc_1 @ 
% 0.85/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.85/1.04      inference('demod', [status(thm)], ['79', '80'])).
% 0.85/1.04  thf('82', plain,
% 0.85/1.04      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.85/1.04         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.85/1.04          | ~ (v2_funct_1 @ X30)
% 0.85/1.04          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.85/1.04          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.85/1.04          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.85/1.04          | ~ (v1_funct_1 @ X30))),
% 0.85/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.85/1.04  thf('83', plain,
% 0.85/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.85/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.85/1.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.85/1.04            = (k2_funct_1 @ sk_C))
% 0.85/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.85/1.04        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.85/1.04            != (k2_relat_1 @ sk_C)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['81', '82'])).
% 0.85/1.04  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('85', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('86', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('87', plain,
% 0.85/1.04      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['85', '86'])).
% 0.85/1.04  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('89', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['87', '88'])).
% 0.85/1.04  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf('91', plain,
% 0.85/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.85/1.04      inference('demod', [status(thm)], ['89', '90'])).
% 0.85/1.04  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('93', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('94', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('95', plain,
% 0.85/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('96', plain,
% 0.85/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04          = (k2_struct_0 @ sk_B))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_A))),
% 0.85/1.04      inference('sup+', [status(thm)], ['94', '95'])).
% 0.85/1.04  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('98', plain,
% 0.85/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['96', '97'])).
% 0.85/1.04  thf('99', plain,
% 0.85/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04          = (k2_struct_0 @ sk_B))
% 0.85/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['93', '98'])).
% 0.85/1.04  thf('100', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('101', plain,
% 0.85/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.85/1.04         = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('demod', [status(thm)], ['99', '100'])).
% 0.85/1.04  thf('102', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf('104', plain,
% 0.85/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.85/1.04         = (k2_relat_1 @ sk_C))),
% 0.85/1.04      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.85/1.04  thf('105', plain,
% 0.85/1.04      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.85/1.04          = (k2_funct_1 @ sk_C))
% 0.85/1.04        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.85/1.04      inference('demod', [status(thm)], ['83', '84', '91', '92', '104'])).
% 0.85/1.04  thf('106', plain,
% 0.85/1.04      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.85/1.04         = (k2_funct_1 @ sk_C))),
% 0.85/1.04      inference('simplify', [status(thm)], ['105'])).
% 0.85/1.04  thf('107', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('108', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('109', plain,
% 0.85/1.04      (![X26 : $i]:
% 0.85/1.04         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.04  thf('110', plain,
% 0.85/1.04      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04          != (k2_struct_0 @ sk_A)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_A))))),
% 0.85/1.04      inference('split', [status(esa)], ['30'])).
% 0.85/1.04  thf('111', plain,
% 0.85/1.04      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04           != (k2_struct_0 @ sk_A))
% 0.85/1.04         | ~ (l1_struct_0 @ sk_A)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_A))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['109', '110'])).
% 0.85/1.04  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('113', plain,
% 0.85/1.04      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04          != (k2_struct_0 @ sk_A)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04                = (k2_struct_0 @ sk_A))))),
% 0.85/1.04      inference('demod', [status(thm)], ['111', '112'])).
% 0.85/1.04  thf('114', plain,
% 0.85/1.04      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.04           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.04           != (k2_struct_0 @ sk_A))
% 0.85/1.04         | ~ (l1_struct_0 @ sk_A)))
% 0.85/1.04         <= (~
% 0.85/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['108', '113'])).
% 0.85/1.05  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('116', plain,
% 0.85/1.05      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05          != (k2_struct_0 @ sk_A)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('demod', [status(thm)], ['114', '115'])).
% 0.85/1.05  thf('117', plain,
% 0.85/1.05      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05           != (k2_struct_0 @ sk_A))
% 0.85/1.05         | ~ (l1_struct_0 @ sk_B)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['107', '116'])).
% 0.85/1.05  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('119', plain,
% 0.85/1.05      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05          != (k2_struct_0 @ sk_A)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('demod', [status(thm)], ['117', '118'])).
% 0.85/1.05  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.05      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.05  thf('121', plain,
% 0.85/1.05      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.85/1.05          != (k2_struct_0 @ sk_A)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('demod', [status(thm)], ['119', '120'])).
% 0.85/1.05  thf('122', plain,
% 0.85/1.05      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['106', '121'])).
% 0.85/1.05  thf('123', plain,
% 0.85/1.05      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['74', '122'])).
% 0.85/1.05  thf('124', plain,
% 0.85/1.05      (((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.85/1.05         | ~ (v1_relat_1 @ sk_C)
% 0.85/1.05         | ~ (v1_funct_1 @ sk_C)
% 0.85/1.05         | ~ (v2_funct_1 @ sk_C)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['65', '123'])).
% 0.85/1.05  thf('125', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.85/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.85/1.05  thf('126', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.85/1.05  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('128', plain, ((v2_funct_1 @ sk_C)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('129', plain,
% 0.85/1.05      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.85/1.05         <= (~
% 0.85/1.05             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05                = (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 0.85/1.05  thf('130', plain,
% 0.85/1.05      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05          = (k2_struct_0 @ sk_A)))),
% 0.85/1.05      inference('simplify', [status(thm)], ['129'])).
% 0.85/1.05  thf('131', plain,
% 0.85/1.05      (~
% 0.85/1.05       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05          = (k2_struct_0 @ sk_B))) | 
% 0.85/1.05       ~
% 0.85/1.05       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05          = (k2_struct_0 @ sk_A)))),
% 0.85/1.05      inference('split', [status(esa)], ['30'])).
% 0.85/1.05  thf('132', plain,
% 0.85/1.05      (~
% 0.85/1.05       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.05          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.85/1.05          = (k2_struct_0 @ sk_B)))),
% 0.85/1.05      inference('sat_resolution*', [status(thm)], ['130', '131'])).
% 0.85/1.05  thf('133', plain,
% 0.85/1.05      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.85/1.05      inference('simpl_trail', [status(thm)], ['64', '132'])).
% 0.85/1.05  thf('134', plain,
% 0.85/1.05      ((m1_subset_1 @ sk_C @ 
% 0.85/1.05        (k1_zfmisc_1 @ 
% 0.85/1.05         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.85/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.85/1.05  thf('135', plain,
% 0.85/1.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.85/1.05         ((v1_funct_2 @ (k2_tops_2 @ X31 @ X32 @ X33) @ X32 @ X31)
% 0.85/1.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.85/1.05          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.85/1.05          | ~ (v1_funct_1 @ X33))),
% 0.85/1.05      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.85/1.05  thf('136', plain,
% 0.85/1.05      ((~ (v1_funct_1 @ sk_C)
% 0.85/1.05        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.85/1.05        | (v1_funct_2 @ 
% 0.85/1.05           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.85/1.05           (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['134', '135'])).
% 0.85/1.05  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('138', plain,
% 0.85/1.05      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.05      inference('demod', [status(thm)], ['51', '52'])).
% 0.85/1.05  thf('139', plain,
% 0.85/1.05      ((v1_funct_2 @ 
% 0.85/1.05        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.85/1.05        (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.85/1.05      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.85/1.05  thf('140', plain,
% 0.85/1.05      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.85/1.05         = (k2_funct_1 @ sk_C))),
% 0.85/1.05      inference('simplify', [status(thm)], ['62'])).
% 0.85/1.05  thf('141', plain,
% 0.85/1.05      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.05        (k2_struct_0 @ sk_A))),
% 0.85/1.05      inference('demod', [status(thm)], ['139', '140'])).
% 0.85/1.05  thf(d1_funct_2, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.85/1.05           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.85/1.05             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.85/1.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.85/1.05           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.85/1.05             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.85/1.05  thf(zf_stmt_1, axiom,
% 0.85/1.05    (![C:$i,B:$i,A:$i]:
% 0.85/1.05     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.85/1.05       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.85/1.05  thf('142', plain,
% 0.85/1.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.85/1.05         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.85/1.05          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.85/1.05          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.85/1.05  thf('143', plain,
% 0.85/1.05      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05           (u1_struct_0 @ sk_B))
% 0.85/1.05        | ((u1_struct_0 @ sk_B)
% 0.85/1.05            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05               (k2_funct_1 @ sk_C))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['141', '142'])).
% 0.85/1.05  thf('144', plain,
% 0.85/1.05      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.85/1.05        (k1_zfmisc_1 @ 
% 0.85/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.85/1.05      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.85/1.05  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.85/1.05  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.85/1.05  thf(zf_stmt_4, axiom,
% 0.85/1.05    (![B:$i,A:$i]:
% 0.85/1.05     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.85/1.05       ( zip_tseitin_0 @ B @ A ) ))).
% 0.85/1.05  thf(zf_stmt_5, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.05       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.85/1.05         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.85/1.05           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.85/1.05             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.85/1.05  thf('145', plain,
% 0.85/1.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.85/1.05         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.85/1.05          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.85/1.05          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.85/1.05  thf('146', plain,
% 0.85/1.05      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05         (u1_struct_0 @ sk_B))
% 0.85/1.05        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['144', '145'])).
% 0.85/1.05  thf('147', plain,
% 0.85/1.05      (![X13 : $i, X14 : $i]:
% 0.85/1.05         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.85/1.05  thf('148', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('149', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.85/1.05      inference('sup+', [status(thm)], ['147', '148'])).
% 0.85/1.05  thf('150', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.85/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.85/1.05  thf(fc8_relat_1, axiom,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.85/1.05       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.85/1.05  thf('151', plain,
% 0.85/1.05      (![X1 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ (k1_relat_1 @ X1))
% 0.85/1.05          | ~ (v1_relat_1 @ X1)
% 0.85/1.05          | (v1_xboole_0 @ X1))),
% 0.85/1.05      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.85/1.05  thf('152', plain,
% 0.85/1.05      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.85/1.05        | (v1_xboole_0 @ sk_C)
% 0.85/1.05        | ~ (v1_relat_1 @ sk_C))),
% 0.85/1.05      inference('sup-', [status(thm)], ['150', '151'])).
% 0.85/1.05  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.85/1.05  thf('154', plain,
% 0.85/1.05      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C))),
% 0.85/1.05      inference('demod', [status(thm)], ['152', '153'])).
% 0.85/1.05  thf(fc11_relat_1, axiom,
% 0.85/1.05    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.85/1.05  thf('155', plain,
% 0.85/1.05      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.85/1.05      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.85/1.05  thf('156', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.05      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.05  thf('157', plain,
% 0.85/1.05      (![X26 : $i]:
% 0.85/1.05         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.85/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.05  thf('158', plain,
% 0.85/1.05      (![X27 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.85/1.05          | ~ (l1_struct_0 @ X27)
% 0.85/1.05          | (v2_struct_0 @ X27))),
% 0.85/1.05      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.85/1.05  thf('159', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.85/1.05          | ~ (l1_struct_0 @ X0)
% 0.85/1.05          | (v2_struct_0 @ X0)
% 0.85/1.05          | ~ (l1_struct_0 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['157', '158'])).
% 0.85/1.05  thf('160', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((v2_struct_0 @ X0)
% 0.85/1.05          | ~ (l1_struct_0 @ X0)
% 0.85/1.05          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.85/1.05      inference('simplify', [status(thm)], ['159'])).
% 0.85/1.05  thf('161', plain,
% 0.85/1.05      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.85/1.05        | ~ (l1_struct_0 @ sk_B)
% 0.85/1.05        | (v2_struct_0 @ sk_B))),
% 0.85/1.05      inference('sup-', [status(thm)], ['156', '160'])).
% 0.85/1.05  thf('162', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('163', plain,
% 0.85/1.05      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.85/1.05      inference('demod', [status(thm)], ['161', '162'])).
% 0.85/1.05  thf('164', plain, (~ (v2_struct_0 @ sk_B)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('165', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.85/1.05      inference('clc', [status(thm)], ['163', '164'])).
% 0.85/1.05  thf('166', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['155', '165'])).
% 0.85/1.05  thf('167', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.85/1.05      inference('clc', [status(thm)], ['154', '166'])).
% 0.85/1.05  thf('168', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ X0)),
% 0.85/1.05      inference('sup-', [status(thm)], ['149', '167'])).
% 0.85/1.05  thf('169', plain,
% 0.85/1.05      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05        (u1_struct_0 @ sk_B))),
% 0.85/1.05      inference('demod', [status(thm)], ['146', '168'])).
% 0.85/1.05  thf('170', plain,
% 0.85/1.05      (((u1_struct_0 @ sk_B)
% 0.85/1.05         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.05            (k2_funct_1 @ sk_C)))),
% 0.85/1.05      inference('demod', [status(thm)], ['143', '169'])).
% 0.85/1.05  thf('171', plain, (((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))),
% 0.85/1.05      inference('demod', [status(thm)], ['133', '170'])).
% 0.85/1.05  thf('172', plain,
% 0.85/1.05      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 0.85/1.05      inference('sup-', [status(thm)], ['0', '171'])).
% 0.85/1.05  thf('173', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.85/1.05      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.05  thf('174', plain, ((l1_struct_0 @ sk_B)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('175', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.85/1.05      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.85/1.05  thf('176', plain, ($false), inference('simplify', [status(thm)], ['175'])).
% 0.85/1.05  
% 0.85/1.05  % SZS output end Refutation
% 0.85/1.05  
% 0.85/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
