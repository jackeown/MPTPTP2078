%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.unYqUQzVqk

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:47 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  232 (1466 expanded)
%              Number of leaves         :   48 ( 450 expanded)
%              Depth                    :   29
%              Number of atoms          : 2359 (35787 expanded)
%              Number of equality atoms :  152 (1845 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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

thf('3',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X26 @ X24 )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('24',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('41',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('57',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('68',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('73',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X30: $i] :
      ( ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','85','86','96'])).

thf('98',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('100',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('101',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','38','39','40','98','112','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('120',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('124',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('127',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['122','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('132',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','132'])).

thf('134',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('135',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X30: $i] :
      ( ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('138',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('139',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','147'])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('156',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('158',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('163',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('166',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','166'])).

thf('168',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('170',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','171'])).

thf('173',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('175',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['173','174'])).

thf('176',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['118','175'])).

thf('177',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,(
    $false ),
    inference(simplify,[status(thm)],['181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.unYqUQzVqk
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.91/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.13  % Solved by: fo/fo7.sh
% 0.91/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.13  % done 447 iterations in 0.660s
% 0.91/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.13  % SZS output start Refutation
% 0.91/1.13  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.13  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.91/1.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.91/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.13  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.13  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.91/1.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.91/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.13  thf(t55_funct_1, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.13       ( ( v2_funct_1 @ A ) =>
% 0.91/1.13         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.91/1.13           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.91/1.13  thf('0', plain,
% 0.91/1.13      (![X1 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X1)
% 0.91/1.13          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.91/1.13          | ~ (v1_funct_1 @ X1)
% 0.91/1.13          | ~ (v1_relat_1 @ X1))),
% 0.91/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.91/1.13  thf(d3_struct_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.91/1.13  thf('1', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('2', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf(t62_tops_2, conjecture,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_struct_0 @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                 ( m1_subset_1 @
% 0.91/1.13                   C @ 
% 0.91/1.13                   ( k1_zfmisc_1 @
% 0.91/1.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13               ( ( ( ( k2_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                   ( v2_funct_1 @ C ) ) =>
% 0.91/1.13                 ( ( ( k1_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.13                       ( k2_tops_2 @
% 0.91/1.13                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.13                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                   ( ( k2_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.13                       ( k2_tops_2 @
% 0.91/1.13                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.13                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.13    (~( ![A:$i]:
% 0.91/1.13        ( ( l1_struct_0 @ A ) =>
% 0.91/1.13          ( ![B:$i]:
% 0.91/1.13            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.91/1.13              ( ![C:$i]:
% 0.91/1.13                ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                    ( v1_funct_2 @
% 0.91/1.13                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                    ( m1_subset_1 @
% 0.91/1.13                      C @ 
% 0.91/1.13                      ( k1_zfmisc_1 @
% 0.91/1.13                        ( k2_zfmisc_1 @
% 0.91/1.13                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13                  ( ( ( ( k2_relset_1 @
% 0.91/1.13                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                        ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                      ( v2_funct_1 @ C ) ) =>
% 0.91/1.13                    ( ( ( k1_relset_1 @
% 0.91/1.13                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.13                          ( k2_tops_2 @
% 0.91/1.13                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.13                        ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                      ( ( k2_relset_1 @
% 0.91/1.13                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.13                          ( k2_tops_2 @
% 0.91/1.13                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.91/1.13                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.91/1.13    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.91/1.13  thf('3', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_B))
% 0.91/1.13        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13            != (k2_struct_0 @ sk_A)))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('4', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('split', [status(esa)], ['3'])).
% 0.91/1.13  thf('5', plain,
% 0.91/1.13      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13           != (k2_struct_0 @ sk_A))
% 0.91/1.13         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['2', '4'])).
% 0.91/1.13  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('7', plain,
% 0.91/1.13      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['5', '6'])).
% 0.91/1.13  thf('8', plain,
% 0.91/1.13      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13           != (k2_struct_0 @ sk_A))
% 0.91/1.13         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['1', '7'])).
% 0.91/1.13  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('10', plain,
% 0.91/1.13      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['8', '9'])).
% 0.91/1.13  thf('11', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.13  thf('12', plain,
% 0.91/1.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.91/1.13         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.91/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.91/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.13  thf('13', plain,
% 0.91/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13         = (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.13  thf('14', plain,
% 0.91/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13         = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('16', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(t132_funct_2, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.13       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.13           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.13         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.91/1.13           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.91/1.13  thf('17', plain,
% 0.91/1.13      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.13         (((X24) = (k1_xboole_0))
% 0.91/1.13          | ~ (v1_funct_1 @ X25)
% 0.91/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.91/1.13          | (v1_partfun1 @ X25 @ X26)
% 0.91/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.91/1.13          | ~ (v1_funct_2 @ X25 @ X26 @ X24)
% 0.91/1.13          | ~ (v1_funct_1 @ X25))),
% 0.91/1.13      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.91/1.13  thf('18', plain,
% 0.91/1.13      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.13         (~ (v1_funct_2 @ X25 @ X26 @ X24)
% 0.91/1.13          | (v1_partfun1 @ X25 @ X26)
% 0.91/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.91/1.13          | ~ (v1_funct_1 @ X25)
% 0.91/1.13          | ((X24) = (k1_xboole_0)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['17'])).
% 0.91/1.13  thf('19', plain,
% 0.91/1.13      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['16', '18'])).
% 0.91/1.13  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('21', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('22', plain,
% 0.91/1.13      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.91/1.13        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.91/1.13      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.91/1.13  thf(d4_partfun1, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.91/1.13       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.91/1.13  thf('23', plain,
% 0.91/1.13      (![X22 : $i, X23 : $i]:
% 0.91/1.13         (~ (v1_partfun1 @ X23 @ X22)
% 0.91/1.13          | ((k1_relat_1 @ X23) = (X22))
% 0.91/1.13          | ~ (v4_relat_1 @ X23 @ X22)
% 0.91/1.13          | ~ (v1_relat_1 @ X23))),
% 0.91/1.13      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.91/1.13  thf('24', plain,
% 0.91/1.13      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.91/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.13        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.91/1.13        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.13  thf('25', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(cc1_relset_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13       ( v1_relat_1 @ C ) ))).
% 0.91/1.13  thf('26', plain,
% 0.91/1.13      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.13         ((v1_relat_1 @ X2)
% 0.91/1.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.91/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.13  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('28', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(cc2_relset_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.13  thf('29', plain,
% 0.91/1.13      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.13         ((v4_relat_1 @ X5 @ X6)
% 0.91/1.13          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.91/1.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.13  thf('30', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.13  thf('31', plain,
% 0.91/1.13      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.91/1.13        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.91/1.13      inference('demod', [status(thm)], ['24', '27', '30'])).
% 0.91/1.13  thf(fc2_struct_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.13       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.13  thf('32', plain,
% 0.91/1.13      (![X32 : $i]:
% 0.91/1.13         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.91/1.13          | ~ (l1_struct_0 @ X32)
% 0.91/1.13          | (v2_struct_0 @ X32))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.91/1.13  thf('33', plain,
% 0.91/1.13      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.13        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.91/1.13        | (v2_struct_0 @ sk_B)
% 0.91/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.13  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.13  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.13  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('36', plain,
% 0.91/1.13      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.91/1.13  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('38', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.13  thf('39', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.13  thf('40', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('41', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('42', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('43', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_C @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.91/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['41', '42'])).
% 0.91/1.13  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('45', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('demod', [status(thm)], ['43', '44'])).
% 0.91/1.13  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('47', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.91/1.13      inference('demod', [status(thm)], ['45', '46'])).
% 0.91/1.13  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.13  thf('49', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.91/1.13      inference('demod', [status(thm)], ['47', '48'])).
% 0.91/1.13  thf(d4_tops_2, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.13       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.91/1.13         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.91/1.13  thf('50', plain,
% 0.91/1.13      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.91/1.13         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.91/1.13          | ~ (v2_funct_1 @ X35)
% 0.91/1.13          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.91/1.13          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.91/1.13          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.91/1.13          | ~ (v1_funct_1 @ X35))),
% 0.91/1.13      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.91/1.13  thf('51', plain,
% 0.91/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.91/1.13        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13            = (k2_funct_1 @ sk_C))
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13            != (k2_relat_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.13  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(d1_funct_2, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.13           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.13             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.13         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.13           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.13             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_1, axiom,
% 0.91/1.13    (![B:$i,A:$i]:
% 0.91/1.13     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.13       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.13  thf('53', plain,
% 0.91/1.13      (![X14 : $i, X15 : $i]:
% 0.91/1.13         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.13  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.13  thf('55', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.13      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.13  thf('56', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('57', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('58', plain,
% 0.91/1.13      (![X32 : $i]:
% 0.91/1.13         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.91/1.13          | ~ (l1_struct_0 @ X32)
% 0.91/1.13          | (v2_struct_0 @ X32))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.91/1.13  thf('59', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.91/1.13          | ~ (l1_struct_0 @ X0)
% 0.91/1.13          | (v2_struct_0 @ X0)
% 0.91/1.13          | ~ (l1_struct_0 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['57', '58'])).
% 0.91/1.13  thf('60', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((v2_struct_0 @ X0)
% 0.91/1.13          | ~ (l1_struct_0 @ X0)
% 0.91/1.13          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['59'])).
% 0.91/1.13  thf('61', plain,
% 0.91/1.13      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.91/1.13        | ~ (l1_struct_0 @ sk_B)
% 0.91/1.13        | (v2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['56', '60'])).
% 0.91/1.13  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('63', plain,
% 0.91/1.13      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)], ['61', '62'])).
% 0.91/1.13  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('65', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('clc', [status(thm)], ['63', '64'])).
% 0.91/1.13  thf('66', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)),
% 0.91/1.13      inference('sup-', [status(thm)], ['55', '65'])).
% 0.91/1.13  thf(t3_funct_2, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.13       ( ( v1_funct_1 @ A ) & 
% 0.91/1.13         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.91/1.13         ( m1_subset_1 @
% 0.91/1.13           A @ 
% 0.91/1.13           ( k1_zfmisc_1 @
% 0.91/1.13             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.91/1.13  thf('67', plain,
% 0.91/1.13      (![X30 : $i]:
% 0.91/1.13         ((m1_subset_1 @ X30 @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.91/1.13          | ~ (v1_funct_1 @ X30)
% 0.91/1.13          | ~ (v1_relat_1 @ X30))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.91/1.13  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.13  thf(zf_stmt_3, axiom,
% 0.91/1.13    (![C:$i,B:$i,A:$i]:
% 0.91/1.13     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.13       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.13  thf(zf_stmt_5, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.13         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.13           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.13             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.13  thf('68', plain,
% 0.91/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.13         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.91/1.13          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.91/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.13  thf('69', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.91/1.13          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['67', '68'])).
% 0.91/1.13  thf('70', plain,
% 0.91/1.13      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.13      inference('sup-', [status(thm)], ['66', '69'])).
% 0.91/1.13  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('73', plain,
% 0.91/1.13      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.91/1.13  thf('74', plain,
% 0.91/1.13      (![X30 : $i]:
% 0.91/1.13         ((v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))
% 0.91/1.13          | ~ (v1_funct_1 @ X30)
% 0.91/1.13          | ~ (v1_relat_1 @ X30))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.91/1.13  thf('75', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.91/1.13          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.91/1.13          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.13  thf('76', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.91/1.13          | ((k1_relat_1 @ X0)
% 0.91/1.13              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['74', '75'])).
% 0.91/1.13  thf('77', plain,
% 0.91/1.13      ((((k1_relat_1 @ sk_C)
% 0.91/1.13          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.13      inference('sup-', [status(thm)], ['73', '76'])).
% 0.91/1.13  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('80', plain,
% 0.91/1.13      (((k1_relat_1 @ sk_C)
% 0.91/1.13         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.91/1.13  thf('81', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.91/1.13          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.91/1.13          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.13  thf('82', plain,
% 0.91/1.13      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.91/1.13        | ~ (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.91/1.13        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['80', '81'])).
% 0.91/1.13  thf('83', plain,
% 0.91/1.13      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.91/1.13  thf('84', plain,
% 0.91/1.13      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.91/1.13        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.91/1.13      inference('demod', [status(thm)], ['82', '83'])).
% 0.91/1.13  thf('85', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('simplify', [status(thm)], ['84'])).
% 0.91/1.13  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('87', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('88', plain,
% 0.91/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13         = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('89', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B))
% 0.91/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['87', '88'])).
% 0.91/1.13  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('91', plain,
% 0.91/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13         = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)], ['89', '90'])).
% 0.91/1.13  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('94', plain,
% 0.91/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13         = (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.91/1.13  thf('95', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.13  thf('96', plain,
% 0.91/1.13      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13         = (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.91/1.13  thf('97', plain,
% 0.91/1.13      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13          = (k2_funct_1 @ sk_C))
% 0.91/1.13        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.91/1.13      inference('demod', [status(thm)], ['51', '52', '85', '86', '96'])).
% 0.91/1.13  thf('98', plain,
% 0.91/1.13      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13         = (k2_funct_1 @ sk_C))),
% 0.91/1.13      inference('simplify', [status(thm)], ['97'])).
% 0.91/1.13  thf('99', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('simplify', [status(thm)], ['84'])).
% 0.91/1.13  thf('100', plain,
% 0.91/1.13      (![X30 : $i]:
% 0.91/1.13         ((m1_subset_1 @ X30 @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.91/1.13          | ~ (v1_funct_1 @ X30)
% 0.91/1.13          | ~ (v1_relat_1 @ X30))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.91/1.13  thf(t31_funct_2, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.13       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.91/1.13         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.91/1.13           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.91/1.13           ( m1_subset_1 @
% 0.91/1.13             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.91/1.13  thf('101', plain,
% 0.91/1.13      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X27)
% 0.91/1.13          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.91/1.13          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.91/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.91/1.13          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.91/1.13          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.91/1.13          | ~ (v1_funct_1 @ X27))),
% 0.91/1.13      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.91/1.13  thf('102', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.91/1.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.91/1.13             (k1_zfmisc_1 @ 
% 0.91/1.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              != (k2_relat_1 @ X0))
% 0.91/1.13          | ~ (v2_funct_1 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['100', '101'])).
% 0.91/1.13  thf('103', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X0)
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              != (k2_relat_1 @ X0))
% 0.91/1.13          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.91/1.13             (k1_zfmisc_1 @ 
% 0.91/1.13              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.91/1.13          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0))),
% 0.91/1.13      inference('simplify', [status(thm)], ['102'])).
% 0.91/1.13  thf('104', plain,
% 0.91/1.13      ((~ (v1_relat_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.91/1.13        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13            != (k2_relat_1 @ sk_C))
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.91/1.13      inference('sup-', [status(thm)], ['99', '103'])).
% 0.91/1.13  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('107', plain,
% 0.91/1.13      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13         = (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['94', '95'])).
% 0.91/1.13  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('109', plain,
% 0.91/1.13      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.13         (k1_zfmisc_1 @ 
% 0.91/1.13          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.91/1.13        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.91/1.13      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.91/1.13  thf('110', plain,
% 0.91/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['109'])).
% 0.91/1.13  thf('111', plain,
% 0.91/1.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.91/1.13         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.91/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.91/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.13  thf('112', plain,
% 0.91/1.13      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.13         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['110', '111'])).
% 0.91/1.13  thf('113', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('114', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.13  thf('115', plain,
% 0.91/1.13      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.13      inference('sup+', [status(thm)], ['113', '114'])).
% 0.91/1.13  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.91/1.13      inference('demod', [status(thm)], ['115', '116'])).
% 0.91/1.13  thf('118', plain,
% 0.91/1.13      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)],
% 0.91/1.13                ['10', '15', '38', '39', '40', '98', '112', '117'])).
% 0.91/1.13  thf('119', plain,
% 0.91/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['109'])).
% 0.91/1.13  thf('120', plain,
% 0.91/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.13         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.91/1.13          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.91/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.13  thf('121', plain,
% 0.91/1.13      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.13         (k2_relat_1 @ sk_C))
% 0.91/1.13        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['119', '120'])).
% 0.91/1.13  thf('122', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.13      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.13  thf('123', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.91/1.13      inference('demod', [status(thm)], ['45', '46'])).
% 0.91/1.13  thf(cc3_relset_1, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( v1_xboole_0 @ A ) =>
% 0.91/1.13       ( ![C:$i]:
% 0.91/1.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13           ( v1_xboole_0 @ C ) ) ) ))).
% 0.91/1.13  thf('124', plain,
% 0.91/1.13      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.13         (~ (v1_xboole_0 @ X8)
% 0.91/1.13          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 0.91/1.13          | (v1_xboole_0 @ X9))),
% 0.91/1.13      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.91/1.13  thf('125', plain,
% 0.91/1.13      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['123', '124'])).
% 0.91/1.13  thf(fc11_relat_1, axiom,
% 0.91/1.13    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.91/1.13  thf('126', plain,
% 0.91/1.13      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.91/1.13  thf('127', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('clc', [status(thm)], ['63', '64'])).
% 0.91/1.13  thf('128', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.91/1.13      inference('sup-', [status(thm)], ['126', '127'])).
% 0.91/1.13  thf('129', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['125', '128'])).
% 0.91/1.13  thf('130', plain, (![X0 : $i]: (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0)),
% 0.91/1.13      inference('sup-', [status(thm)], ['122', '129'])).
% 0.91/1.13  thf('131', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.13  thf('132', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 0.91/1.13      inference('demod', [status(thm)], ['130', '131'])).
% 0.91/1.13  thf('133', plain,
% 0.91/1.13      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.13        (k2_relat_1 @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['121', '132'])).
% 0.91/1.13  thf('134', plain,
% 0.91/1.13      (![X30 : $i]:
% 0.91/1.13         ((m1_subset_1 @ X30 @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.91/1.13          | ~ (v1_funct_1 @ X30)
% 0.91/1.13          | ~ (v1_relat_1 @ X30))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.91/1.13  thf('135', plain,
% 0.91/1.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.91/1.13         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.91/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.91/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.13  thf('136', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              = (k2_relat_1 @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['134', '135'])).
% 0.91/1.13  thf('137', plain,
% 0.91/1.13      (![X30 : $i]:
% 0.91/1.13         ((v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))
% 0.91/1.13          | ~ (v1_funct_1 @ X30)
% 0.91/1.13          | ~ (v1_relat_1 @ X30))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.91/1.13  thf('138', plain,
% 0.91/1.13      (![X30 : $i]:
% 0.91/1.13         ((m1_subset_1 @ X30 @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.91/1.13          | ~ (v1_funct_1 @ X30)
% 0.91/1.13          | ~ (v1_relat_1 @ X30))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.91/1.13  thf('139', plain,
% 0.91/1.13      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X27)
% 0.91/1.13          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 0.91/1.13          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.91/1.13          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.91/1.13          | ~ (v1_funct_1 @ X27))),
% 0.91/1.13      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.91/1.13  thf('140', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.91/1.13             (k1_relat_1 @ X0))
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              != (k2_relat_1 @ X0))
% 0.91/1.13          | ~ (v2_funct_1 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['138', '139'])).
% 0.91/1.13  thf('141', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X0)
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              != (k2_relat_1 @ X0))
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.91/1.13             (k1_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0))),
% 0.91/1.13      inference('simplify', [status(thm)], ['140'])).
% 0.91/1.13  thf('142', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.91/1.13             (k1_relat_1 @ X0))
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              != (k2_relat_1 @ X0))
% 0.91/1.13          | ~ (v2_funct_1 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['137', '141'])).
% 0.91/1.13  thf('143', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X0)
% 0.91/1.13          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.91/1.13              != (k2_relat_1 @ X0))
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.91/1.13             (k1_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0))),
% 0.91/1.13      inference('simplify', [status(thm)], ['142'])).
% 0.91/1.13  thf('144', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0)
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.91/1.13             (k1_relat_1 @ X0))
% 0.91/1.13          | ~ (v2_funct_1 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['136', '143'])).
% 0.91/1.13  thf('145', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v2_funct_1 @ X0)
% 0.91/1.13          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.91/1.13             (k1_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v1_funct_1 @ X0))),
% 0.91/1.13      inference('simplify', [status(thm)], ['144'])).
% 0.91/1.13  thf('146', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.91/1.13          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.91/1.13          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.13  thf('147', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (v1_funct_1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ X0)
% 0.91/1.13          | ~ (v2_funct_1 @ X0)
% 0.91/1.13          | ~ (zip_tseitin_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.91/1.13               (k2_relat_1 @ X0))
% 0.91/1.13          | ((k2_relat_1 @ X0)
% 0.91/1.13              = (k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.91/1.13                 (k2_funct_1 @ X0))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['145', '146'])).
% 0.91/1.13  thf('148', plain,
% 0.91/1.13      ((((k2_relat_1 @ sk_C)
% 0.91/1.13          = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.13             (k2_funct_1 @ sk_C)))
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.13      inference('sup-', [status(thm)], ['133', '147'])).
% 0.91/1.13  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('152', plain,
% 0.91/1.13      (((k2_relat_1 @ sk_C)
% 0.91/1.13         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.13            (k2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 0.91/1.13  thf('153', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('154', plain,
% 0.91/1.13      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.91/1.13         = (k2_funct_1 @ sk_C))),
% 0.91/1.13      inference('simplify', [status(thm)], ['97'])).
% 0.91/1.13  thf('155', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.13  thf('156', plain,
% 0.91/1.13      (![X31 : $i]:
% 0.91/1.13         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.13  thf('157', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_B)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('split', [status(esa)], ['3'])).
% 0.91/1.13  thf('158', plain,
% 0.91/1.13      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13           != (k2_struct_0 @ sk_B))
% 0.91/1.13         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['156', '157'])).
% 0.91/1.13  thf('159', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('160', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_B)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13                = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('demod', [status(thm)], ['158', '159'])).
% 0.91/1.13  thf('161', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.91/1.13          != (k2_struct_0 @ sk_B)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['155', '160'])).
% 0.91/1.14  thf('162', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.14  thf('163', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.91/1.14          != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['161', '162'])).
% 0.91/1.14  thf('164', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.14      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('165', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.91/1.14      inference('clc', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('166', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.14          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.91/1.14          != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.91/1.14  thf('167', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.14          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['154', '166'])).
% 0.91/1.14  thf('168', plain,
% 0.91/1.14      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.14           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.91/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['153', '167'])).
% 0.91/1.14  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.14  thf('170', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('171', plain,
% 0.91/1.14      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.91/1.14          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.91/1.14  thf('172', plain,
% 0.91/1.14      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14                = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['152', '171'])).
% 0.91/1.14  thf('173', plain,
% 0.91/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_B)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['172'])).
% 0.91/1.14  thf('174', plain,
% 0.91/1.14      (~
% 0.91/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_A))) | 
% 0.91/1.14       ~
% 0.91/1.14       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_B)))),
% 0.91/1.14      inference('split', [status(esa)], ['3'])).
% 0.91/1.14  thf('175', plain,
% 0.91/1.14      (~
% 0.91/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          = (k2_struct_0 @ sk_A)))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)], ['173', '174'])).
% 0.91/1.14  thf('176', plain,
% 0.91/1.14      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['118', '175'])).
% 0.91/1.14  thf('177', plain,
% 0.91/1.14      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.91/1.14        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.91/1.14      inference('sup-', [status(thm)], ['0', '176'])).
% 0.91/1.14  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.14      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.14  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('181', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 0.91/1.14  thf('182', plain, ($false), inference('simplify', [status(thm)], ['181'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.91/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
