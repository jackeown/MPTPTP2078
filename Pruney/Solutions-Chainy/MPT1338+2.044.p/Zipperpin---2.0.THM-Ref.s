%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.146VdxpsTJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:54 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 888 expanded)
%              Number of leaves         :   44 ( 276 expanded)
%              Depth                    :   15
%              Number of atoms          : 1937 (22395 expanded)
%              Number of equality atoms :  151 (1240 expanded)
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

thf('6',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('40',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

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

thf('47',plain,(
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

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','56','65','66','74'])).

thf('76',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('78',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('80',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('81',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_relset_1 @ X15 @ X16 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('84',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('87',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('89',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','64'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('100',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','37','38','39','78','97','102'])).

thf('104',plain,
    ( $false
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('106',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('107',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('109',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('110',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','114'])).

thf('116',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('117',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('119',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('120',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('128',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['128','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
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

thf('140',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['142','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['155','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','152','153','154','166'])).

thf('168',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127','168','169'])).

thf('171',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','170'])).

thf('172',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('174',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['104','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.146VdxpsTJ
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:30:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.29/1.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.29/1.50  % Solved by: fo/fo7.sh
% 1.29/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.50  % done 466 iterations in 1.030s
% 1.29/1.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.29/1.50  % SZS output start Refutation
% 1.29/1.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.29/1.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.29/1.50  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.29/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.50  thf(sk_C_type, type, sk_C: $i).
% 1.29/1.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.29/1.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.29/1.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.29/1.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.29/1.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.29/1.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.29/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.29/1.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.29/1.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.29/1.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.29/1.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.29/1.50  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.29/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.29/1.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.29/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.29/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.29/1.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.29/1.50  thf(d3_struct_0, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.29/1.50  thf('0', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf(t62_tops_2, conjecture,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( l1_struct_0 @ A ) =>
% 1.29/1.50       ( ![B:$i]:
% 1.29/1.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.29/1.50           ( ![C:$i]:
% 1.29/1.50             ( ( ( v1_funct_1 @ C ) & 
% 1.29/1.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.50                 ( m1_subset_1 @
% 1.29/1.50                   C @ 
% 1.29/1.50                   ( k1_zfmisc_1 @
% 1.29/1.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.50               ( ( ( ( k2_relset_1 @
% 1.29/1.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.29/1.50                     ( k2_struct_0 @ B ) ) & 
% 1.29/1.50                   ( v2_funct_1 @ C ) ) =>
% 1.29/1.50                 ( ( ( k1_relset_1 @
% 1.29/1.50                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.50                       ( k2_tops_2 @
% 1.29/1.50                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.50                     ( k2_struct_0 @ B ) ) & 
% 1.29/1.50                   ( ( k2_relset_1 @
% 1.29/1.50                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.50                       ( k2_tops_2 @
% 1.29/1.50                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.50                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.29/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.50    (~( ![A:$i]:
% 1.29/1.50        ( ( l1_struct_0 @ A ) =>
% 1.29/1.50          ( ![B:$i]:
% 1.29/1.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.29/1.50              ( ![C:$i]:
% 1.29/1.50                ( ( ( v1_funct_1 @ C ) & 
% 1.29/1.50                    ( v1_funct_2 @
% 1.29/1.50                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.50                    ( m1_subset_1 @
% 1.29/1.50                      C @ 
% 1.29/1.50                      ( k1_zfmisc_1 @
% 1.29/1.50                        ( k2_zfmisc_1 @
% 1.29/1.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.50                  ( ( ( ( k2_relset_1 @
% 1.29/1.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.29/1.50                        ( k2_struct_0 @ B ) ) & 
% 1.29/1.50                      ( v2_funct_1 @ C ) ) =>
% 1.29/1.50                    ( ( ( k1_relset_1 @
% 1.29/1.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.50                          ( k2_tops_2 @
% 1.29/1.50                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.50                        ( k2_struct_0 @ B ) ) & 
% 1.29/1.50                      ( ( k2_relset_1 @
% 1.29/1.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.50                          ( k2_tops_2 @
% 1.29/1.50                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.50                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.29/1.50    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.29/1.50  thf('1', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B))
% 1.29/1.50        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50            != (k2_struct_0 @ sk_A)))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('2', plain,
% 1.29/1.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_A)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('split', [status(esa)], ['1'])).
% 1.29/1.50  thf('3', plain,
% 1.29/1.50      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50           != (k2_struct_0 @ sk_A))
% 1.29/1.50         | ~ (l1_struct_0 @ sk_B)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['0', '2'])).
% 1.29/1.50  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('5', plain,
% 1.29/1.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_A)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('demod', [status(thm)], ['3', '4'])).
% 1.29/1.50  thf('6', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf(d1_funct_2, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.29/1.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.29/1.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.29/1.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.29/1.50  thf(zf_stmt_1, axiom,
% 1.29/1.50    (![B:$i,A:$i]:
% 1.29/1.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.50       ( zip_tseitin_0 @ B @ A ) ))).
% 1.29/1.50  thf('7', plain,
% 1.29/1.50      (![X17 : $i, X18 : $i]:
% 1.29/1.50         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.29/1.50  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.29/1.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.29/1.50  thf('9', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.29/1.50      inference('sup+', [status(thm)], ['7', '8'])).
% 1.29/1.50  thf('10', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.29/1.50  thf(zf_stmt_3, axiom,
% 1.29/1.50    (![C:$i,B:$i,A:$i]:
% 1.29/1.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.29/1.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.29/1.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.29/1.50  thf(zf_stmt_5, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.29/1.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.29/1.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.29/1.50  thf('11', plain,
% 1.29/1.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.29/1.50         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.29/1.50          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.29/1.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.29/1.50  thf('12', plain,
% 1.29/1.50      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.50        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['10', '11'])).
% 1.29/1.50  thf('13', plain,
% 1.29/1.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.50        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['9', '12'])).
% 1.29/1.50  thf('14', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('15', plain,
% 1.29/1.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.29/1.50         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.29/1.50          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.29/1.50          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.29/1.50  thf('16', plain,
% 1.29/1.50      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.50        | ((u1_struct_0 @ sk_A)
% 1.29/1.50            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.50  thf('17', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(redefinition_k1_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.29/1.50  thf('18', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.50         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.29/1.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.50  thf('19', plain,
% 1.29/1.50      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['17', '18'])).
% 1.29/1.50  thf('20', plain,
% 1.29/1.50      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.50        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['16', '19'])).
% 1.29/1.50  thf('21', plain,
% 1.29/1.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.50        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['13', '20'])).
% 1.29/1.50  thf('22', plain,
% 1.29/1.50      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B)
% 1.29/1.50        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['6', '21'])).
% 1.29/1.50  thf('23', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(redefinition_k2_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.29/1.50  thf('24', plain,
% 1.29/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.29/1.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.29/1.50  thf('25', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['23', '24'])).
% 1.29/1.50  thf('26', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('29', plain,
% 1.29/1.50      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['22', '27', '28'])).
% 1.29/1.50  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf(fc5_struct_0, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.29/1.50       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.29/1.50  thf('31', plain,
% 1.29/1.50      (![X26 : $i]:
% 1.29/1.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 1.29/1.50          | ~ (l1_struct_0 @ X26)
% 1.29/1.50          | (v2_struct_0 @ X26))),
% 1.29/1.50      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.29/1.50  thf('32', plain,
% 1.29/1.50      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | (v2_struct_0 @ sk_B)
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup-', [status(thm)], ['30', '31'])).
% 1.29/1.50  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('34', plain,
% 1.29/1.50      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['32', '33'])).
% 1.29/1.50  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('36', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['34', '35'])).
% 1.29/1.50  thf('37', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['29', '36'])).
% 1.29/1.50  thf('38', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['29', '36'])).
% 1.29/1.50  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('40', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('41', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('42', plain,
% 1.29/1.50      (((m1_subset_1 @ sk_C @ 
% 1.29/1.50         (k1_zfmisc_1 @ 
% 1.29/1.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['40', '41'])).
% 1.29/1.50  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('44', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('demod', [status(thm)], ['42', '43'])).
% 1.29/1.50  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('46', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['44', '45'])).
% 1.29/1.50  thf(d4_tops_2, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.50       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.29/1.50         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.29/1.50  thf('47', plain,
% 1.29/1.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.29/1.50          | ~ (v2_funct_1 @ X29)
% 1.29/1.50          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.29/1.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.29/1.50          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.29/1.50          | ~ (v1_funct_1 @ X29))),
% 1.29/1.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.29/1.50  thf('48', plain,
% 1.29/1.50      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C)
% 1.29/1.50        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['46', '47'])).
% 1.29/1.50  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('50', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('51', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('52', plain,
% 1.29/1.50      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['50', '51'])).
% 1.29/1.50  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('54', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['52', '53'])).
% 1.29/1.50  thf('55', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('56', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['54', '55'])).
% 1.29/1.50  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(d9_funct_1, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.29/1.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.29/1.50  thf('58', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         (~ (v2_funct_1 @ X0)
% 1.29/1.50          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 1.29/1.50          | ~ (v1_funct_1 @ X0)
% 1.29/1.50          | ~ (v1_relat_1 @ X0))),
% 1.29/1.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.29/1.50  thf('59', plain,
% 1.29/1.50      ((~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['57', '58'])).
% 1.29/1.50  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('61', plain,
% 1.29/1.50      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['59', '60'])).
% 1.29/1.50  thf('62', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(cc1_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( v1_relat_1 @ C ) ))).
% 1.29/1.50  thf('63', plain,
% 1.29/1.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.29/1.50         ((v1_relat_1 @ X2)
% 1.29/1.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.29/1.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.29/1.50  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.50      inference('sup-', [status(thm)], ['62', '63'])).
% 1.29/1.50  thf('65', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['61', '64'])).
% 1.29/1.50  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('67', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('68', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('69', plain,
% 1.29/1.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50          = (k2_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['67', '68'])).
% 1.29/1.50  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('71', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['69', '70'])).
% 1.29/1.50  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('74', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.29/1.50  thf('75', plain,
% 1.29/1.50      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50          = (k4_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['48', '49', '56', '65', '66', '74'])).
% 1.29/1.50  thf('76', plain,
% 1.29/1.50      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('simplify', [status(thm)], ['75'])).
% 1.29/1.50  thf('77', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['29', '36'])).
% 1.29/1.50  thf('78', plain,
% 1.29/1.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['76', '77'])).
% 1.29/1.50  thf('79', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(dt_k3_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( m1_subset_1 @
% 1.29/1.50         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.29/1.50         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.29/1.50  thf('80', plain,
% 1.29/1.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.29/1.50         ((m1_subset_1 @ (k3_relset_1 @ X5 @ X6 @ X7) @ 
% 1.29/1.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 1.29/1.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.29/1.50      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.29/1.50  thf('81', plain,
% 1.29/1.50      ((m1_subset_1 @ 
% 1.29/1.50        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['79', '80'])).
% 1.29/1.50  thf('82', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(redefinition_k3_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.29/1.50  thf('83', plain,
% 1.29/1.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.29/1.50         (((k3_relset_1 @ X15 @ X16 @ X14) = (k4_relat_1 @ X14))
% 1.29/1.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.29/1.50  thf('84', plain,
% 1.29/1.50      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['82', '83'])).
% 1.29/1.50  thf('85', plain,
% 1.29/1.50      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.50      inference('demod', [status(thm)], ['81', '84'])).
% 1.29/1.50  thf('86', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['29', '36'])).
% 1.29/1.50  thf('87', plain,
% 1.29/1.50      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['85', '86'])).
% 1.29/1.50  thf('88', plain,
% 1.29/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.29/1.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.29/1.50  thf('89', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['87', '88'])).
% 1.29/1.50  thf('90', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['61', '64'])).
% 1.29/1.50  thf(t55_funct_1, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.29/1.50       ( ( v2_funct_1 @ A ) =>
% 1.29/1.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.29/1.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.29/1.50  thf('91', plain,
% 1.29/1.50      (![X1 : $i]:
% 1.29/1.50         (~ (v2_funct_1 @ X1)
% 1.29/1.50          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.29/1.50          | ~ (v1_funct_1 @ X1)
% 1.29/1.50          | ~ (v1_relat_1 @ X1))),
% 1.29/1.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.29/1.50  thf('92', plain,
% 1.29/1.50      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.29/1.50        | ~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.50      inference('sup+', [status(thm)], ['90', '91'])).
% 1.29/1.50  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.50      inference('sup-', [status(thm)], ['62', '63'])).
% 1.29/1.50  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('96', plain,
% 1.29/1.50      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 1.29/1.50  thf('97', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['89', '96'])).
% 1.29/1.50  thf('98', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('99', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['29', '36'])).
% 1.29/1.50  thf('100', plain,
% 1.29/1.50      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['98', '99'])).
% 1.29/1.50  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('102', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['100', '101'])).
% 1.29/1.50  thf('103', plain,
% 1.29/1.50      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('demod', [status(thm)],
% 1.29/1.50                ['5', '37', '38', '39', '78', '97', '102'])).
% 1.29/1.50  thf('104', plain,
% 1.29/1.50      (($false)
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('simplify', [status(thm)], ['103'])).
% 1.29/1.50  thf('105', plain,
% 1.29/1.50      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['85', '86'])).
% 1.29/1.50  thf('106', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.50         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.29/1.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.50  thf('107', plain,
% 1.29/1.50      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['105', '106'])).
% 1.29/1.50  thf('108', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['61', '64'])).
% 1.29/1.50  thf('109', plain,
% 1.29/1.50      (![X1 : $i]:
% 1.29/1.50         (~ (v2_funct_1 @ X1)
% 1.29/1.50          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.29/1.50          | ~ (v1_funct_1 @ X1)
% 1.29/1.50          | ~ (v1_relat_1 @ X1))),
% 1.29/1.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.29/1.50  thf('110', plain,
% 1.29/1.50      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.29/1.50        | ~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.50      inference('sup+', [status(thm)], ['108', '109'])).
% 1.29/1.50  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.50      inference('sup-', [status(thm)], ['62', '63'])).
% 1.29/1.50  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('114', plain,
% 1.29/1.50      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 1.29/1.50  thf('115', plain,
% 1.29/1.50      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['107', '114'])).
% 1.29/1.50  thf('116', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('clc', [status(thm)], ['29', '36'])).
% 1.29/1.50  thf('117', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('118', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('119', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('split', [status(esa)], ['1'])).
% 1.29/1.50  thf('120', plain,
% 1.29/1.50      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50           != (k2_struct_0 @ sk_B))
% 1.29/1.50         | ~ (l1_struct_0 @ sk_A)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['118', '119'])).
% 1.29/1.50  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('122', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('demod', [status(thm)], ['120', '121'])).
% 1.29/1.50  thf('123', plain,
% 1.29/1.50      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50           != (k2_struct_0 @ sk_B))
% 1.29/1.50         | ~ (l1_struct_0 @ sk_B)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['117', '122'])).
% 1.29/1.50  thf('124', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('125', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('demod', [status(thm)], ['123', '124'])).
% 1.29/1.50  thf('126', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['116', '125'])).
% 1.29/1.50  thf('127', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('128', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('129', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('130', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('131', plain,
% 1.29/1.50      (((m1_subset_1 @ sk_C @ 
% 1.29/1.50         (k1_zfmisc_1 @ 
% 1.29/1.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['129', '130'])).
% 1.29/1.50  thf('132', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('133', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.50      inference('demod', [status(thm)], ['131', '132'])).
% 1.29/1.50  thf('134', plain,
% 1.29/1.50      (((m1_subset_1 @ sk_C @ 
% 1.29/1.50         (k1_zfmisc_1 @ 
% 1.29/1.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['128', '133'])).
% 1.29/1.50  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('136', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('demod', [status(thm)], ['134', '135'])).
% 1.29/1.50  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('138', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['136', '137'])).
% 1.29/1.50  thf('139', plain,
% 1.29/1.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.29/1.50          | ~ (v2_funct_1 @ X29)
% 1.29/1.50          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.29/1.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.29/1.50          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.29/1.50          | ~ (v1_funct_1 @ X29))),
% 1.29/1.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.29/1.50  thf('140', plain,
% 1.29/1.50      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C)
% 1.29/1.50        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['138', '139'])).
% 1.29/1.50  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('142', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('143', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('144', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('145', plain,
% 1.29/1.50      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['143', '144'])).
% 1.29/1.50  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('147', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['145', '146'])).
% 1.29/1.50  thf('148', plain,
% 1.29/1.50      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['142', '147'])).
% 1.29/1.50  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('150', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['148', '149'])).
% 1.29/1.50  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('152', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['150', '151'])).
% 1.29/1.50  thf('153', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['61', '64'])).
% 1.29/1.50  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('155', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('156', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('157', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('158', plain,
% 1.29/1.50      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50          = (k2_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['156', '157'])).
% 1.29/1.50  thf('159', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('160', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['158', '159'])).
% 1.29/1.50  thf('161', plain,
% 1.29/1.50      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50          = (k2_struct_0 @ sk_B))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['155', '160'])).
% 1.29/1.50  thf('162', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('163', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('demod', [status(thm)], ['161', '162'])).
% 1.29/1.50  thf('164', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('165', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('166', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['163', '164', '165'])).
% 1.29/1.50  thf('167', plain,
% 1.29/1.50      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50          = (k4_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)],
% 1.29/1.50                ['140', '141', '152', '153', '154', '166'])).
% 1.29/1.50  thf('168', plain,
% 1.29/1.50      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k4_relat_1 @ sk_C))),
% 1.29/1.50      inference('simplify', [status(thm)], ['167'])).
% 1.29/1.50  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('170', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('demod', [status(thm)], ['126', '127', '168', '169'])).
% 1.29/1.50  thf('171', plain,
% 1.29/1.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['115', '170'])).
% 1.29/1.50  thf('172', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_B)))),
% 1.29/1.50      inference('simplify', [status(thm)], ['171'])).
% 1.29/1.50  thf('173', plain,
% 1.29/1.50      (~
% 1.29/1.50       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_A))) | 
% 1.29/1.50       ~
% 1.29/1.50       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_B)))),
% 1.29/1.50      inference('split', [status(esa)], ['1'])).
% 1.29/1.50  thf('174', plain,
% 1.29/1.50      (~
% 1.29/1.50       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sat_resolution*', [status(thm)], ['172', '173'])).
% 1.29/1.50  thf('175', plain, ($false),
% 1.29/1.50      inference('simpl_trail', [status(thm)], ['104', '174'])).
% 1.29/1.50  
% 1.29/1.50  % SZS output end Refutation
% 1.29/1.50  
% 1.29/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
