%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.120MJcJ1jT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:02 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 735 expanded)
%              Number of leaves         :   45 ( 236 expanded)
%              Depth                    :   16
%              Number of atoms          : 1554 (17730 expanded)
%              Number of equality atoms :  125 ( 997 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k3_relset_1 @ X16 @ X17 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['5','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','16'])).

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

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','37'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','45'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

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

thf('67',plain,(
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

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','69','76','77','85'])).

thf('87',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('89',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

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
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','59','89','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','37'])).

thf('97',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('101',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('106',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('108',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('113',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('116',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('117',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','117'])).

thf('119',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('121',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['119','120'])).

thf('122',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['95','121'])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.120MJcJ1jT
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.94/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.94/1.16  % Solved by: fo/fo7.sh
% 0.94/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.94/1.16  % done 425 iterations in 0.700s
% 0.94/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.94/1.16  % SZS output start Refutation
% 0.94/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.94/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.94/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.94/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.94/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.94/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.94/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.94/1.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.94/1.16  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.94/1.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.94/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.94/1.16  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.94/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.94/1.16  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.94/1.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.94/1.16  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.94/1.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.94/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.94/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.94/1.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.94/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.94/1.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.94/1.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.94/1.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.94/1.16  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.94/1.16  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.94/1.16  thf(t62_tops_2, conjecture,
% 0.94/1.16    (![A:$i]:
% 0.94/1.16     ( ( l1_struct_0 @ A ) =>
% 0.94/1.16       ( ![B:$i]:
% 0.94/1.16         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.94/1.16           ( ![C:$i]:
% 0.94/1.16             ( ( ( v1_funct_1 @ C ) & 
% 0.94/1.16                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.94/1.16                 ( m1_subset_1 @
% 0.94/1.16                   C @ 
% 0.94/1.16                   ( k1_zfmisc_1 @
% 0.94/1.16                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.94/1.16               ( ( ( ( k2_relset_1 @
% 0.94/1.16                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.94/1.16                     ( k2_struct_0 @ B ) ) & 
% 0.94/1.16                   ( v2_funct_1 @ C ) ) =>
% 0.94/1.16                 ( ( ( k1_relset_1 @
% 0.94/1.16                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.94/1.16                       ( k2_tops_2 @
% 0.94/1.16                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.94/1.16                     ( k2_struct_0 @ B ) ) & 
% 0.94/1.16                   ( ( k2_relset_1 @
% 0.94/1.16                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.94/1.16                       ( k2_tops_2 @
% 0.94/1.16                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.94/1.16                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.94/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.94/1.16    (~( ![A:$i]:
% 0.94/1.16        ( ( l1_struct_0 @ A ) =>
% 0.94/1.16          ( ![B:$i]:
% 0.94/1.16            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.94/1.16              ( ![C:$i]:
% 0.94/1.16                ( ( ( v1_funct_1 @ C ) & 
% 0.94/1.16                    ( v1_funct_2 @
% 0.94/1.16                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.94/1.16                    ( m1_subset_1 @
% 0.94/1.16                      C @ 
% 0.94/1.16                      ( k1_zfmisc_1 @
% 0.94/1.16                        ( k2_zfmisc_1 @
% 0.94/1.16                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.94/1.16                  ( ( ( ( k2_relset_1 @
% 0.94/1.16                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.94/1.16                        ( k2_struct_0 @ B ) ) & 
% 0.94/1.16                      ( v2_funct_1 @ C ) ) =>
% 0.94/1.16                    ( ( ( k1_relset_1 @
% 0.94/1.16                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.94/1.16                          ( k2_tops_2 @
% 0.94/1.16                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.94/1.16                        ( k2_struct_0 @ B ) ) & 
% 0.94/1.16                      ( ( k2_relset_1 @
% 0.94/1.16                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.94/1.16                          ( k2_tops_2 @
% 0.94/1.16                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.94/1.16                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.94/1.16    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.94/1.16  thf('0', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf(dt_k3_relset_1, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.16       ( m1_subset_1 @
% 0.94/1.16         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.94/1.16         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.94/1.16  thf('1', plain,
% 0.94/1.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.94/1.16         ((m1_subset_1 @ (k3_relset_1 @ X6 @ X7 @ X8) @ 
% 0.94/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.94/1.16          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.94/1.16      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.94/1.16  thf('2', plain,
% 0.94/1.16      ((m1_subset_1 @ 
% 0.94/1.16        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.94/1.16      inference('sup-', [status(thm)], ['0', '1'])).
% 0.94/1.16  thf('3', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf(redefinition_k3_relset_1, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.16       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.94/1.16  thf('4', plain,
% 0.94/1.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.94/1.16         (((k3_relset_1 @ X16 @ X17 @ X15) = (k4_relat_1 @ X15))
% 0.94/1.16          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.94/1.16      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.94/1.16  thf('5', plain,
% 0.94/1.16      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k4_relat_1 @ sk_C))),
% 0.94/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.94/1.16  thf('6', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf(cc2_relat_1, axiom,
% 0.94/1.16    (![A:$i]:
% 0.94/1.16     ( ( v1_relat_1 @ A ) =>
% 0.94/1.16       ( ![B:$i]:
% 0.94/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.94/1.16  thf('7', plain,
% 0.94/1.16      (![X0 : $i, X1 : $i]:
% 0.94/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.94/1.16          | (v1_relat_1 @ X0)
% 0.94/1.16          | ~ (v1_relat_1 @ X1))),
% 0.94/1.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.94/1.16  thf('8', plain,
% 0.94/1.16      ((~ (v1_relat_1 @ 
% 0.94/1.16           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.94/1.16        | (v1_relat_1 @ sk_C))),
% 0.94/1.16      inference('sup-', [status(thm)], ['6', '7'])).
% 0.94/1.16  thf(fc6_relat_1, axiom,
% 0.94/1.16    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.94/1.16  thf('9', plain,
% 0.94/1.16      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.94/1.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.94/1.16  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.94/1.16      inference('demod', [status(thm)], ['8', '9'])).
% 0.94/1.16  thf(d9_funct_1, axiom,
% 0.94/1.16    (![A:$i]:
% 0.94/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.94/1.16       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.94/1.16  thf('11', plain,
% 0.94/1.16      (![X5 : $i]:
% 0.94/1.16         (~ (v2_funct_1 @ X5)
% 0.94/1.16          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.94/1.16          | ~ (v1_funct_1 @ X5)
% 0.94/1.16          | ~ (v1_relat_1 @ X5))),
% 0.94/1.16      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.94/1.16  thf('12', plain,
% 0.94/1.16      ((~ (v1_funct_1 @ sk_C)
% 0.94/1.16        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.94/1.16        | ~ (v2_funct_1 @ sk_C))),
% 0.94/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.94/1.16  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('15', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.94/1.16  thf('16', plain,
% 0.94/1.16      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k2_funct_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['5', '15'])).
% 0.94/1.16  thf('17', plain,
% 0.94/1.16      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.94/1.16      inference('demod', [status(thm)], ['2', '16'])).
% 0.94/1.16  thf(d1_funct_2, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.16       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.94/1.16           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.94/1.16             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.94/1.16         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.94/1.16           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.94/1.16             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.94/1.16  thf(zf_stmt_1, axiom,
% 0.94/1.16    (![B:$i,A:$i]:
% 0.94/1.16     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.94/1.16       ( zip_tseitin_0 @ B @ A ) ))).
% 0.94/1.16  thf('18', plain,
% 0.94/1.16      (![X18 : $i, X19 : $i]:
% 0.94/1.16         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.94/1.16  thf('19', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.94/1.16  thf(zf_stmt_3, axiom,
% 0.94/1.16    (![C:$i,B:$i,A:$i]:
% 0.94/1.16     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.94/1.16       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.94/1.16  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.94/1.16  thf(zf_stmt_5, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.16       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.94/1.16         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.94/1.16           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.94/1.16             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.94/1.16  thf('20', plain,
% 0.94/1.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.94/1.16         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.94/1.16          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.94/1.16          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.94/1.16  thf('21', plain,
% 0.94/1.16      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.94/1.16        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['19', '20'])).
% 0.94/1.16  thf('22', plain,
% 0.94/1.16      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.94/1.16        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['18', '21'])).
% 0.94/1.16  thf('23', plain,
% 0.94/1.16      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('24', plain,
% 0.94/1.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.94/1.16         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.94/1.16          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.94/1.16          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.94/1.16  thf('25', plain,
% 0.94/1.16      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.94/1.16        | ((u1_struct_0 @ sk_A)
% 0.94/1.16            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['23', '24'])).
% 0.94/1.16  thf('26', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf(redefinition_k1_relset_1, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.94/1.16  thf('27', plain,
% 0.94/1.16      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.94/1.16         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.94/1.16          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.94/1.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.94/1.16  thf('28', plain,
% 0.94/1.16      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('sup-', [status(thm)], ['26', '27'])).
% 0.94/1.16  thf('29', plain,
% 0.94/1.16      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.94/1.16        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.94/1.16      inference('demod', [status(thm)], ['25', '28'])).
% 0.94/1.16  thf('30', plain,
% 0.94/1.16      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.94/1.16        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['22', '29'])).
% 0.94/1.16  thf(fc2_struct_0, axiom,
% 0.94/1.16    (![A:$i]:
% 0.94/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.94/1.16       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.94/1.16  thf('31', plain,
% 0.94/1.16      (![X27 : $i]:
% 0.94/1.16         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.94/1.16          | ~ (l1_struct_0 @ X27)
% 0.94/1.16          | (v2_struct_0 @ X27))),
% 0.94/1.16      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.94/1.16  thf('32', plain,
% 0.94/1.16      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.94/1.16        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.94/1.16        | (v2_struct_0 @ sk_B)
% 0.94/1.16        | ~ (l1_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup-', [status(thm)], ['30', '31'])).
% 0.94/1.16  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.94/1.16  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.94/1.16      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.94/1.16  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('35', plain,
% 0.94/1.16      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.94/1.16      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.94/1.16  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('37', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('38', plain,
% 0.94/1.16      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.94/1.16      inference('demod', [status(thm)], ['17', '37'])).
% 0.94/1.16  thf(redefinition_k2_relset_1, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.94/1.16       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.94/1.16  thf('39', plain,
% 0.94/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.94/1.16         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.94/1.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.94/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.94/1.16  thf('40', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['38', '39'])).
% 0.94/1.16  thf('41', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.94/1.16  thf(t37_relat_1, axiom,
% 0.94/1.16    (![A:$i]:
% 0.94/1.16     ( ( v1_relat_1 @ A ) =>
% 0.94/1.16       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.94/1.16         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.94/1.16  thf('42', plain,
% 0.94/1.16      (![X4 : $i]:
% 0.94/1.16         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.94/1.16          | ~ (v1_relat_1 @ X4))),
% 0.94/1.16      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.94/1.16  thf('43', plain,
% 0.94/1.16      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.94/1.16        | ~ (v1_relat_1 @ sk_C))),
% 0.94/1.16      inference('sup+', [status(thm)], ['41', '42'])).
% 0.94/1.16  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.94/1.16      inference('demod', [status(thm)], ['8', '9'])).
% 0.94/1.16  thf('45', plain,
% 0.94/1.16      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.94/1.16      inference('demod', [status(thm)], ['43', '44'])).
% 0.94/1.16  thf('46', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['40', '45'])).
% 0.94/1.16  thf(d3_struct_0, axiom,
% 0.94/1.16    (![A:$i]:
% 0.94/1.16     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.94/1.16  thf('47', plain,
% 0.94/1.16      (![X26 : $i]:
% 0.94/1.16         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.94/1.16      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.94/1.16  thf('48', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          != (k2_struct_0 @ sk_B))
% 0.94/1.16        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16            != (k2_struct_0 @ sk_A)))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('49', plain,
% 0.94/1.16      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          != (k2_struct_0 @ sk_A)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_A))))),
% 0.94/1.16      inference('split', [status(esa)], ['48'])).
% 0.94/1.16  thf('50', plain,
% 0.94/1.16      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16           != (k2_struct_0 @ sk_A))
% 0.94/1.16         | ~ (l1_struct_0 @ sk_B)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_A))))),
% 0.94/1.16      inference('sup-', [status(thm)], ['47', '49'])).
% 0.94/1.16  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('52', plain,
% 0.94/1.16      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          != (k2_struct_0 @ sk_A)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_A))))),
% 0.94/1.16      inference('demod', [status(thm)], ['50', '51'])).
% 0.94/1.16  thf('53', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('54', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('55', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('56', plain,
% 0.94/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.94/1.16         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.94/1.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.94/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.94/1.16  thf('57', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k2_relat_1 @ sk_C))),
% 0.94/1.16      inference('sup-', [status(thm)], ['55', '56'])).
% 0.94/1.16  thf('58', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('59', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('60', plain,
% 0.94/1.16      (![X26 : $i]:
% 0.94/1.16         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.94/1.16      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.94/1.16  thf('61', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('62', plain,
% 0.94/1.16      (((m1_subset_1 @ sk_C @ 
% 0.94/1.16         (k1_zfmisc_1 @ 
% 0.94/1.16          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.94/1.16        | ~ (l1_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['60', '61'])).
% 0.94/1.16  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('64', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('demod', [status(thm)], ['62', '63'])).
% 0.94/1.16  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('66', plain,
% 0.94/1.16      ((m1_subset_1 @ sk_C @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.94/1.16      inference('demod', [status(thm)], ['64', '65'])).
% 0.94/1.16  thf(d4_tops_2, axiom,
% 0.94/1.16    (![A:$i,B:$i,C:$i]:
% 0.94/1.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.94/1.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.94/1.16       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.94/1.16         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.94/1.16  thf('67', plain,
% 0.94/1.16      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.94/1.16         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.94/1.16          | ~ (v2_funct_1 @ X30)
% 0.94/1.16          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.94/1.16          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.94/1.16          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.94/1.16          | ~ (v1_funct_1 @ X30))),
% 0.94/1.16      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.94/1.16  thf('68', plain,
% 0.94/1.16      ((~ (v1_funct_1 @ sk_C)
% 0.94/1.16        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.94/1.16        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16            = (k2_funct_1 @ sk_C))
% 0.94/1.16        | ~ (v2_funct_1 @ sk_C)
% 0.94/1.16        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16            != (k2_relat_1 @ sk_C)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['66', '67'])).
% 0.94/1.16  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('70', plain,
% 0.94/1.16      (![X26 : $i]:
% 0.94/1.16         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.94/1.16      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.94/1.16  thf('71', plain,
% 0.94/1.16      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('72', plain,
% 0.94/1.16      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.94/1.16        | ~ (l1_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['70', '71'])).
% 0.94/1.16  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('74', plain,
% 0.94/1.16      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('demod', [status(thm)], ['72', '73'])).
% 0.94/1.16  thf('75', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('76', plain,
% 0.94/1.16      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['74', '75'])).
% 0.94/1.16  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('78', plain,
% 0.94/1.16      (![X26 : $i]:
% 0.94/1.16         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.94/1.16      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.94/1.16  thf('79', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('80', plain,
% 0.94/1.16      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16          = (k2_struct_0 @ sk_B))
% 0.94/1.16        | ~ (l1_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['78', '79'])).
% 0.94/1.16  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('82', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.94/1.16         = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('demod', [status(thm)], ['80', '81'])).
% 0.94/1.16  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('85', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16         = (k2_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.94/1.16  thf('86', plain,
% 0.94/1.16      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16          = (k2_funct_1 @ sk_C))
% 0.94/1.16        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.94/1.16      inference('demod', [status(thm)], ['68', '69', '76', '77', '85'])).
% 0.94/1.16  thf('87', plain,
% 0.94/1.16      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16         = (k2_funct_1 @ sk_C))),
% 0.94/1.16      inference('simplify', [status(thm)], ['86'])).
% 0.94/1.16  thf('88', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('89', plain,
% 0.94/1.16      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16         = (k2_funct_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['87', '88'])).
% 0.94/1.16  thf('90', plain,
% 0.94/1.16      (![X26 : $i]:
% 0.94/1.16         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.94/1.16      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.94/1.16  thf('91', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('92', plain,
% 0.94/1.16      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 0.94/1.16      inference('sup+', [status(thm)], ['90', '91'])).
% 0.94/1.16  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('94', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['92', '93'])).
% 0.94/1.16  thf('95', plain,
% 0.94/1.16      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_A))))),
% 0.94/1.16      inference('demod', [status(thm)], ['52', '53', '54', '59', '89', '94'])).
% 0.94/1.16  thf('96', plain,
% 0.94/1.16      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.94/1.16        (k1_zfmisc_1 @ 
% 0.94/1.16         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.94/1.16      inference('demod', [status(thm)], ['17', '37'])).
% 0.94/1.16  thf('97', plain,
% 0.94/1.16      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.94/1.16         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.94/1.16          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.94/1.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.94/1.16  thf('98', plain,
% 0.94/1.16      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.94/1.16      inference('sup-', [status(thm)], ['96', '97'])).
% 0.94/1.16  thf('99', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.94/1.16  thf('100', plain,
% 0.94/1.16      (![X4 : $i]:
% 0.94/1.16         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.94/1.16          | ~ (v1_relat_1 @ X4))),
% 0.94/1.16      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.94/1.16  thf('101', plain,
% 0.94/1.16      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.94/1.16        | ~ (v1_relat_1 @ sk_C))),
% 0.94/1.16      inference('sup+', [status(thm)], ['99', '100'])).
% 0.94/1.16  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.94/1.16      inference('demod', [status(thm)], ['8', '9'])).
% 0.94/1.16  thf('103', plain,
% 0.94/1.16      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.94/1.16      inference('demod', [status(thm)], ['101', '102'])).
% 0.94/1.16  thf('104', plain,
% 0.94/1.16      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['98', '103'])).
% 0.94/1.16  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('106', plain,
% 0.94/1.16      (![X26 : $i]:
% 0.94/1.16         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.94/1.16      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.94/1.16  thf('107', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          != (k2_struct_0 @ sk_B)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('split', [status(esa)], ['48'])).
% 0.94/1.16  thf('108', plain,
% 0.94/1.16      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16           != (k2_struct_0 @ sk_B))
% 0.94/1.16         | ~ (l1_struct_0 @ sk_B)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('sup-', [status(thm)], ['106', '107'])).
% 0.94/1.16  thf('109', plain, ((l1_struct_0 @ sk_B)),
% 0.94/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.16  thf('110', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          != (k2_struct_0 @ sk_B)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('demod', [status(thm)], ['108', '109'])).
% 0.94/1.16  thf('111', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.94/1.16          != (k2_struct_0 @ sk_B)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('sup-', [status(thm)], ['105', '110'])).
% 0.94/1.16  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.94/1.16      inference('sup+', [status(thm)], ['57', '58'])).
% 0.94/1.16  thf('113', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.94/1.16          != (k2_relat_1 @ sk_C)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('demod', [status(thm)], ['111', '112'])).
% 0.94/1.16  thf('114', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('115', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.94/1.16  thf('116', plain,
% 0.94/1.16      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.94/1.16         = (k2_funct_1 @ sk_C))),
% 0.94/1.16      inference('demod', [status(thm)], ['87', '88'])).
% 0.94/1.16  thf('117', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.94/1.16  thf('118', plain,
% 0.94/1.16      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.94/1.16         <= (~
% 0.94/1.16             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16                = (k2_struct_0 @ sk_B))))),
% 0.94/1.16      inference('sup-', [status(thm)], ['104', '117'])).
% 0.94/1.16  thf('119', plain,
% 0.94/1.16      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          = (k2_struct_0 @ sk_B)))),
% 0.94/1.16      inference('simplify', [status(thm)], ['118'])).
% 0.94/1.16  thf('120', plain,
% 0.94/1.16      (~
% 0.94/1.16       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          = (k2_struct_0 @ sk_A))) | 
% 0.94/1.16       ~
% 0.94/1.16       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          = (k2_struct_0 @ sk_B)))),
% 0.94/1.16      inference('split', [status(esa)], ['48'])).
% 0.94/1.16  thf('121', plain,
% 0.94/1.16      (~
% 0.94/1.16       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.94/1.16          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.94/1.16          = (k2_struct_0 @ sk_A)))),
% 0.94/1.16      inference('sat_resolution*', [status(thm)], ['119', '120'])).
% 0.94/1.16  thf('122', plain,
% 0.94/1.16      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.94/1.16         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.94/1.16      inference('simpl_trail', [status(thm)], ['95', '121'])).
% 0.94/1.16  thf('123', plain, ($false),
% 0.94/1.16      inference('simplify_reflect-', [status(thm)], ['46', '122'])).
% 0.94/1.16  
% 0.94/1.16  % SZS output end Refutation
% 0.94/1.16  
% 0.99/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
