%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9KdyNLTVUr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:02 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 866 expanded)
%              Number of leaves         :   45 ( 270 expanded)
%              Depth                    :   16
%              Number of atoms          : 1610 (21351 expanded)
%              Number of equality atoms :  127 (1180 expanded)
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
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

thf('54',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('55',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('68',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

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

thf('75',plain,(
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

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','84','85','93'])).

thf('95',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('97',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['41','48'])).

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
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','97','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','49'])).

thf('105',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('106',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('108',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('109',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','111'])).

thf('113',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('115',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf('117',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('124',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','124'])).

thf('126',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','125'])).

thf('127',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf('129',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['103','129'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9KdyNLTVUr
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.07/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.24  % Solved by: fo/fo7.sh
% 1.07/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.24  % done 482 iterations in 0.818s
% 1.07/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.24  % SZS output start Refutation
% 1.07/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.07/1.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.07/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.24  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.07/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.24  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.07/1.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.07/1.24  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.07/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.07/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.24  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.07/1.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.24  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.07/1.24  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.07/1.24  thf(t62_tops_2, conjecture,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( l1_struct_0 @ A ) =>
% 1.07/1.24       ( ![B:$i]:
% 1.07/1.24         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.07/1.24           ( ![C:$i]:
% 1.07/1.24             ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.24                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.24                 ( m1_subset_1 @
% 1.07/1.24                   C @ 
% 1.07/1.24                   ( k1_zfmisc_1 @
% 1.07/1.24                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.24               ( ( ( ( k2_relset_1 @
% 1.07/1.24                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.07/1.24                     ( k2_struct_0 @ B ) ) & 
% 1.07/1.24                   ( v2_funct_1 @ C ) ) =>
% 1.07/1.24                 ( ( ( k1_relset_1 @
% 1.07/1.24                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.24                       ( k2_tops_2 @
% 1.07/1.24                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.24                     ( k2_struct_0 @ B ) ) & 
% 1.07/1.24                   ( ( k2_relset_1 @
% 1.07/1.24                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.24                       ( k2_tops_2 @
% 1.07/1.24                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.24                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.07/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.24    (~( ![A:$i]:
% 1.07/1.24        ( ( l1_struct_0 @ A ) =>
% 1.07/1.24          ( ![B:$i]:
% 1.07/1.24            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.07/1.24              ( ![C:$i]:
% 1.07/1.24                ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.24                    ( v1_funct_2 @
% 1.07/1.24                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.24                    ( m1_subset_1 @
% 1.07/1.24                      C @ 
% 1.07/1.24                      ( k1_zfmisc_1 @
% 1.07/1.24                        ( k2_zfmisc_1 @
% 1.07/1.24                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.24                  ( ( ( ( k2_relset_1 @
% 1.07/1.24                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.07/1.24                        ( k2_struct_0 @ B ) ) & 
% 1.07/1.24                      ( v2_funct_1 @ C ) ) =>
% 1.07/1.24                    ( ( ( k1_relset_1 @
% 1.07/1.24                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.24                          ( k2_tops_2 @
% 1.07/1.24                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.24                        ( k2_struct_0 @ B ) ) & 
% 1.07/1.24                      ( ( k2_relset_1 @
% 1.07/1.24                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.24                          ( k2_tops_2 @
% 1.07/1.24                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.24                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.07/1.24    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.07/1.24  thf('0', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(dt_k3_relset_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( m1_subset_1 @
% 1.07/1.24         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.07/1.24         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.07/1.24  thf('1', plain,
% 1.07/1.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.24         ((m1_subset_1 @ (k3_relset_1 @ X6 @ X7 @ X8) @ 
% 1.07/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 1.07/1.24          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.07/1.24      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.07/1.24  thf('2', plain,
% 1.07/1.24      ((m1_subset_1 @ 
% 1.07/1.24        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.07/1.24  thf('3', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(redefinition_k3_relset_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.07/1.24  thf('4', plain,
% 1.07/1.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.07/1.24         (((k3_relset_1 @ X16 @ X17 @ X15) = (k4_relat_1 @ X15))
% 1.07/1.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.07/1.24      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.07/1.24  thf('5', plain,
% 1.07/1.24      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k4_relat_1 @ sk_C))),
% 1.07/1.24      inference('sup-', [status(thm)], ['3', '4'])).
% 1.07/1.24  thf('6', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(cc2_relat_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( v1_relat_1 @ A ) =>
% 1.07/1.24       ( ![B:$i]:
% 1.07/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.24  thf('7', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.24          | (v1_relat_1 @ X0)
% 1.07/1.24          | ~ (v1_relat_1 @ X1))),
% 1.07/1.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.24  thf('8', plain,
% 1.07/1.24      ((~ (v1_relat_1 @ 
% 1.07/1.24           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.07/1.24        | (v1_relat_1 @ sk_C))),
% 1.07/1.24      inference('sup-', [status(thm)], ['6', '7'])).
% 1.07/1.24  thf(fc6_relat_1, axiom,
% 1.07/1.24    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.24  thf('9', plain,
% 1.07/1.24      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.07/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.24  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.24      inference('demod', [status(thm)], ['8', '9'])).
% 1.07/1.24  thf(d9_funct_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.24       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.07/1.24  thf('11', plain,
% 1.07/1.24      (![X5 : $i]:
% 1.07/1.24         (~ (v2_funct_1 @ X5)
% 1.07/1.24          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.07/1.24          | ~ (v1_funct_1 @ X5)
% 1.07/1.24          | ~ (v1_relat_1 @ X5))),
% 1.07/1.24      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.07/1.24  thf('12', plain,
% 1.07/1.24      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.24        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.07/1.24        | ~ (v2_funct_1 @ sk_C))),
% 1.07/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.07/1.24  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('15', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.07/1.24  thf('16', plain,
% 1.07/1.24      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k2_funct_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['5', '15'])).
% 1.07/1.24  thf('17', plain,
% 1.07/1.24      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.07/1.24      inference('demod', [status(thm)], ['2', '16'])).
% 1.07/1.24  thf(d3_struct_0, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.07/1.24  thf('18', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf(d1_funct_2, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.07/1.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.07/1.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.07/1.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.07/1.24  thf(zf_stmt_1, axiom,
% 1.07/1.24    (![B:$i,A:$i]:
% 1.07/1.24     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.24       ( zip_tseitin_0 @ B @ A ) ))).
% 1.07/1.24  thf('19', plain,
% 1.07/1.24      (![X18 : $i, X19 : $i]:
% 1.07/1.24         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.07/1.24  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.07/1.24  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('21', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.07/1.24      inference('sup+', [status(thm)], ['19', '20'])).
% 1.07/1.24  thf('22', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.07/1.24  thf(zf_stmt_3, axiom,
% 1.07/1.24    (![C:$i,B:$i,A:$i]:
% 1.07/1.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.07/1.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.07/1.24  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.24  thf(zf_stmt_5, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.07/1.24         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.24           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.07/1.24             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.07/1.24  thf('23', plain,
% 1.07/1.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.07/1.24         (~ (zip_tseitin_0 @ X23 @ X24)
% 1.07/1.24          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 1.07/1.24          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.24  thf('24', plain,
% 1.07/1.24      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.07/1.24        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['22', '23'])).
% 1.07/1.24  thf('25', plain,
% 1.07/1.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.24        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['21', '24'])).
% 1.07/1.24  thf('26', plain,
% 1.07/1.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('27', plain,
% 1.07/1.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.24         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 1.07/1.24          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 1.07/1.24          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.07/1.24  thf('28', plain,
% 1.07/1.24      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.07/1.24        | ((u1_struct_0 @ sk_A)
% 1.07/1.24            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['26', '27'])).
% 1.07/1.24  thf('29', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(redefinition_k1_relset_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.07/1.24  thf('30', plain,
% 1.07/1.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.24         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 1.07/1.24          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.07/1.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.07/1.24  thf('31', plain,
% 1.07/1.24      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('sup-', [status(thm)], ['29', '30'])).
% 1.07/1.24  thf('32', plain,
% 1.07/1.24      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.07/1.24        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.07/1.24      inference('demod', [status(thm)], ['28', '31'])).
% 1.07/1.24  thf('33', plain,
% 1.07/1.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.24        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['25', '32'])).
% 1.07/1.24  thf('34', plain,
% 1.07/1.24      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.07/1.24        | ~ (l1_struct_0 @ sk_B)
% 1.07/1.24        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.07/1.24      inference('sup+', [status(thm)], ['18', '33'])).
% 1.07/1.24  thf('35', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.24  thf('36', plain,
% 1.07/1.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.24         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.07/1.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.24  thf('37', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k2_relat_1 @ sk_C))),
% 1.07/1.24      inference('sup-', [status(thm)], ['35', '36'])).
% 1.07/1.24  thf('38', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('41', plain,
% 1.07/1.24      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.07/1.24        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.07/1.24      inference('demod', [status(thm)], ['34', '39', '40'])).
% 1.07/1.24  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf(fc5_struct_0, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.07/1.24       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.07/1.24  thf('43', plain,
% 1.07/1.24      (![X27 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ (k2_struct_0 @ X27))
% 1.07/1.24          | ~ (l1_struct_0 @ X27)
% 1.07/1.24          | (v2_struct_0 @ X27))),
% 1.07/1.24      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.07/1.24  thf('44', plain,
% 1.07/1.24      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.07/1.24        | (v2_struct_0 @ sk_B)
% 1.07/1.24        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup-', [status(thm)], ['42', '43'])).
% 1.07/1.24  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('46', plain,
% 1.07/1.24      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.07/1.24      inference('demod', [status(thm)], ['44', '45'])).
% 1.07/1.24  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('48', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['46', '47'])).
% 1.07/1.24  thf('49', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['41', '48'])).
% 1.07/1.24  thf('50', plain,
% 1.07/1.24      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.24      inference('demod', [status(thm)], ['17', '49'])).
% 1.07/1.24  thf('51', plain,
% 1.07/1.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.24         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.07/1.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.24  thf('52', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.24  thf('53', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.07/1.24  thf(t37_relat_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( v1_relat_1 @ A ) =>
% 1.07/1.24       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.07/1.24         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.07/1.24  thf('54', plain,
% 1.07/1.24      (![X4 : $i]:
% 1.07/1.24         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 1.07/1.24          | ~ (v1_relat_1 @ X4))),
% 1.07/1.24      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.07/1.24  thf('55', plain,
% 1.07/1.24      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.07/1.24        | ~ (v1_relat_1 @ sk_C))),
% 1.07/1.24      inference('sup+', [status(thm)], ['53', '54'])).
% 1.07/1.24  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.24      inference('demod', [status(thm)], ['8', '9'])).
% 1.07/1.24  thf('57', plain,
% 1.07/1.24      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.24      inference('demod', [status(thm)], ['55', '56'])).
% 1.07/1.24  thf('58', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['52', '57'])).
% 1.07/1.24  thf('59', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf('60', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          != (k2_struct_0 @ sk_B))
% 1.07/1.24        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24            != (k2_struct_0 @ sk_A)))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('61', plain,
% 1.07/1.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          != (k2_struct_0 @ sk_A)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_A))))),
% 1.07/1.24      inference('split', [status(esa)], ['60'])).
% 1.07/1.24  thf('62', plain,
% 1.07/1.24      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24           != (k2_struct_0 @ sk_A))
% 1.07/1.24         | ~ (l1_struct_0 @ sk_B)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_A))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['59', '61'])).
% 1.07/1.24  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('64', plain,
% 1.07/1.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          != (k2_struct_0 @ sk_A)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_A))))),
% 1.07/1.24      inference('demod', [status(thm)], ['62', '63'])).
% 1.07/1.24  thf('65', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['41', '48'])).
% 1.07/1.24  thf('66', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['41', '48'])).
% 1.07/1.24  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('68', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf('69', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('70', plain,
% 1.07/1.24      (((m1_subset_1 @ sk_C @ 
% 1.07/1.24         (k1_zfmisc_1 @ 
% 1.07/1.24          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.07/1.24        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['68', '69'])).
% 1.07/1.24  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('72', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('demod', [status(thm)], ['70', '71'])).
% 1.07/1.24  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('74', plain,
% 1.07/1.24      ((m1_subset_1 @ sk_C @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.07/1.24      inference('demod', [status(thm)], ['72', '73'])).
% 1.07/1.24  thf(d4_tops_2, axiom,
% 1.07/1.24    (![A:$i,B:$i,C:$i]:
% 1.07/1.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.24       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.07/1.24         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.07/1.24  thf('75', plain,
% 1.07/1.24      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.07/1.24         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 1.07/1.24          | ~ (v2_funct_1 @ X30)
% 1.07/1.24          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 1.07/1.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.07/1.24          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 1.07/1.24          | ~ (v1_funct_1 @ X30))),
% 1.07/1.24      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.07/1.24  thf('76', plain,
% 1.07/1.24      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.24        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.07/1.24        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24            = (k2_funct_1 @ sk_C))
% 1.07/1.24        | ~ (v2_funct_1 @ sk_C)
% 1.07/1.24        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24            != (k2_relat_1 @ sk_C)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['74', '75'])).
% 1.07/1.24  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('78', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf('79', plain,
% 1.07/1.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('80', plain,
% 1.07/1.24      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.07/1.24        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['78', '79'])).
% 1.07/1.24  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('82', plain,
% 1.07/1.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('demod', [status(thm)], ['80', '81'])).
% 1.07/1.24  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('84', plain,
% 1.07/1.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['82', '83'])).
% 1.07/1.24  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('86', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf('87', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('88', plain,
% 1.07/1.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24          = (k2_struct_0 @ sk_B))
% 1.07/1.24        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['86', '87'])).
% 1.07/1.24  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('90', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.07/1.24         = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('demod', [status(thm)], ['88', '89'])).
% 1.07/1.24  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('93', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24         = (k2_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.07/1.24  thf('94', plain,
% 1.07/1.24      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24          = (k2_funct_1 @ sk_C))
% 1.07/1.24        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.07/1.24      inference('demod', [status(thm)], ['76', '77', '84', '85', '93'])).
% 1.07/1.24  thf('95', plain,
% 1.07/1.24      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24         = (k2_funct_1 @ sk_C))),
% 1.07/1.24      inference('simplify', [status(thm)], ['94'])).
% 1.07/1.24  thf('96', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['41', '48'])).
% 1.07/1.24  thf('97', plain,
% 1.07/1.24      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24         = (k2_funct_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['95', '96'])).
% 1.07/1.24  thf('98', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf('99', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['41', '48'])).
% 1.07/1.24  thf('100', plain,
% 1.07/1.24      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.24      inference('sup+', [status(thm)], ['98', '99'])).
% 1.07/1.24  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('102', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['100', '101'])).
% 1.07/1.24  thf('103', plain,
% 1.07/1.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_A))))),
% 1.07/1.24      inference('demod', [status(thm)], ['64', '65', '66', '67', '97', '102'])).
% 1.07/1.24  thf('104', plain,
% 1.07/1.24      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.24        (k1_zfmisc_1 @ 
% 1.07/1.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.24      inference('demod', [status(thm)], ['17', '49'])).
% 1.07/1.24  thf('105', plain,
% 1.07/1.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.24         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 1.07/1.24          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.07/1.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.07/1.24  thf('106', plain,
% 1.07/1.24      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['104', '105'])).
% 1.07/1.24  thf('107', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.07/1.24  thf('108', plain,
% 1.07/1.24      (![X4 : $i]:
% 1.07/1.24         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 1.07/1.24          | ~ (v1_relat_1 @ X4))),
% 1.07/1.24      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.07/1.24  thf('109', plain,
% 1.07/1.24      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.07/1.24        | ~ (v1_relat_1 @ sk_C))),
% 1.07/1.24      inference('sup+', [status(thm)], ['107', '108'])).
% 1.07/1.24  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.24      inference('demod', [status(thm)], ['8', '9'])).
% 1.07/1.24  thf('111', plain,
% 1.07/1.24      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.24      inference('demod', [status(thm)], ['109', '110'])).
% 1.07/1.24  thf('112', plain,
% 1.07/1.24      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.07/1.24      inference('demod', [status(thm)], ['106', '111'])).
% 1.07/1.24  thf('113', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('clc', [status(thm)], ['41', '48'])).
% 1.07/1.24  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('115', plain,
% 1.07/1.24      (![X26 : $i]:
% 1.07/1.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.07/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.24  thf('116', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          != (k2_struct_0 @ sk_B)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('split', [status(esa)], ['60'])).
% 1.07/1.24  thf('117', plain,
% 1.07/1.24      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24           != (k2_struct_0 @ sk_B))
% 1.07/1.24         | ~ (l1_struct_0 @ sk_B)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['115', '116'])).
% 1.07/1.24  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('119', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          != (k2_struct_0 @ sk_B)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('demod', [status(thm)], ['117', '118'])).
% 1.07/1.24  thf('120', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.07/1.24          != (k2_struct_0 @ sk_B)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['114', '119'])).
% 1.07/1.24  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '38'])).
% 1.07/1.24  thf('122', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.07/1.24          != (k2_relat_1 @ sk_C)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('demod', [status(thm)], ['120', '121'])).
% 1.07/1.24  thf('123', plain,
% 1.07/1.24      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.24         = (k2_funct_1 @ sk_C))),
% 1.07/1.24      inference('simplify', [status(thm)], ['94'])).
% 1.07/1.24  thf('124', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('demod', [status(thm)], ['122', '123'])).
% 1.07/1.24  thf('125', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['113', '124'])).
% 1.07/1.24  thf('126', plain,
% 1.07/1.24      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.07/1.24         <= (~
% 1.07/1.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24                = (k2_struct_0 @ sk_B))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['112', '125'])).
% 1.07/1.24  thf('127', plain,
% 1.07/1.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          = (k2_struct_0 @ sk_B)))),
% 1.07/1.24      inference('simplify', [status(thm)], ['126'])).
% 1.07/1.24  thf('128', plain,
% 1.07/1.24      (~
% 1.07/1.24       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          = (k2_struct_0 @ sk_A))) | 
% 1.07/1.24       ~
% 1.07/1.24       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          = (k2_struct_0 @ sk_B)))),
% 1.07/1.24      inference('split', [status(esa)], ['60'])).
% 1.07/1.24  thf('129', plain,
% 1.07/1.24      (~
% 1.07/1.24       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.24          = (k2_struct_0 @ sk_A)))),
% 1.07/1.24      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 1.07/1.24  thf('130', plain,
% 1.07/1.24      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.24         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.07/1.24      inference('simpl_trail', [status(thm)], ['103', '129'])).
% 1.07/1.24  thf('131', plain, ($false),
% 1.07/1.24      inference('simplify_reflect-', [status(thm)], ['58', '130'])).
% 1.07/1.24  
% 1.07/1.24  % SZS output end Refutation
% 1.07/1.24  
% 1.07/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
