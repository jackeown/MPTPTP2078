%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r4kJRB801s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:46 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  332 (1627 expanded)
%              Number of leaves         :   48 ( 489 expanded)
%              Depth                    :   27
%              Number of atoms          : 3378 (39048 expanded)
%              Number of equality atoms :  179 (1965 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
       != X29 )
      | ( v1_partfun1 @ X30 @ X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v4_relat_1 @ X30 @ ( k1_relat_1 @ X30 ) )
      | ( v1_partfun1 @ X30 @ ( k1_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('22',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( v1_partfun1 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','33'])).

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

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['46','47','48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

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

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('62',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('65',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('67',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','76'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('84',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('92',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('100',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('105',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('112',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('118',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','118'])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','118'])).

thf('121',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','119','120'])).

thf('122',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('124',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('128',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('131',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('132',plain,(
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

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('141',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['85'])).

thf('144',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('146',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('149',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','149'])).

thf('151',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('153',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('156',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('158',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('162',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('164',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('168',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','168'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','168'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','168'])).

thf('172',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','169','170','171'])).

thf('173',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','172'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('177',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','177'])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('180',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('181',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','181'])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('186',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('191',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['85'])).

thf('194',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['192','193'])).

thf('195',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['121','194'])).

thf('196',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','195'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('198',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('199',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('200',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('201',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('202',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('204',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('205',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('207',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('208',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['205','208'])).

thf('210',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['202','209'])).

thf('211',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['199','210'])).

thf('212',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('213',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('214',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('215',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('217',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['212','217'])).

thf('219',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('220',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('222',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('224',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('226',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('227',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('229',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('231',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('233',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('235',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['224','235'])).

thf('237',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('238',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['211','236','237'])).

thf('239',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','238'])).

thf('240',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','168'])).

thf('241',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
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

thf('243',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('245',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('246',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('247',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['245','248'])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('251',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('252',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('254',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['252','255'])).

thf('257',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('258',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('259',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('261',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('263',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('266',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('267',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('268',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['266','267'])).

thf('269',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('270',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('272',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('273',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['270','271','272'])).

thf('274',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['211','236','237'])).

thf('275',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','168'])).

thf('277',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['243','244','264','265','277'])).

thf('279',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('281',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['196','197','279','280'])).

thf('282',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r4kJRB801s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:56:03 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.89/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.12  % Solved by: fo/fo7.sh
% 0.89/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.12  % done 406 iterations in 0.666s
% 0.89/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.12  % SZS output start Refutation
% 0.89/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.12  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.89/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.12  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.89/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.89/1.12  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.89/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.89/1.12  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.89/1.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.89/1.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.89/1.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.12  thf(d1_funct_2, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.89/1.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.89/1.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.89/1.12  thf(zf_stmt_0, axiom,
% 0.89/1.12    (![B:$i,A:$i]:
% 0.89/1.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.12       ( zip_tseitin_0 @ B @ A ) ))).
% 0.89/1.12  thf('0', plain,
% 0.89/1.12      (![X21 : $i, X22 : $i]:
% 0.89/1.12         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.89/1.12  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.12  thf('2', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.89/1.12      inference('sup+', [status(thm)], ['0', '1'])).
% 0.89/1.12  thf(dt_k2_funct_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.12       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.89/1.12         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.89/1.12  thf('3', plain,
% 0.89/1.12      (![X4 : $i]:
% 0.89/1.12         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.89/1.12          | ~ (v1_funct_1 @ X4)
% 0.89/1.12          | ~ (v1_relat_1 @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.12  thf('4', plain,
% 0.89/1.12      (![X4 : $i]:
% 0.89/1.12         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.89/1.12          | ~ (v1_funct_1 @ X4)
% 0.89/1.12          | ~ (v1_relat_1 @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.12  thf(t55_funct_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.12       ( ( v2_funct_1 @ A ) =>
% 0.89/1.12         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.89/1.12           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.12  thf('5', plain,
% 0.89/1.12      (![X5 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X5)
% 0.89/1.12          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.89/1.12          | ~ (v1_funct_1 @ X5)
% 0.89/1.12          | ~ (v1_relat_1 @ X5))),
% 0.89/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.12  thf(t3_funct_2, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.12       ( ( v1_funct_1 @ A ) & 
% 0.89/1.12         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.89/1.12         ( m1_subset_1 @
% 0.89/1.12           A @ 
% 0.89/1.12           ( k1_zfmisc_1 @
% 0.89/1.12             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.12  thf('6', plain,
% 0.89/1.12      (![X31 : $i]:
% 0.89/1.12         ((m1_subset_1 @ X31 @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 0.89/1.12          | ~ (v1_funct_1 @ X31)
% 0.89/1.12          | ~ (v1_relat_1 @ X31))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.12  thf(cc2_relset_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.89/1.12  thf('7', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((v4_relat_1 @ X9 @ X10)
% 0.89/1.12          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.12  thf('8', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.12  thf(d4_partfun1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.89/1.12       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.89/1.12  thf('9', plain,
% 0.89/1.12      (![X29 : $i, X30 : $i]:
% 0.89/1.12         (((k1_relat_1 @ X30) != (X29))
% 0.89/1.12          | (v1_partfun1 @ X30 @ X29)
% 0.89/1.12          | ~ (v4_relat_1 @ X30 @ X29)
% 0.89/1.12          | ~ (v1_relat_1 @ X30))),
% 0.89/1.12      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.89/1.12  thf('10', plain,
% 0.89/1.12      (![X30 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X30)
% 0.89/1.12          | ~ (v4_relat_1 @ X30 @ (k1_relat_1 @ X30))
% 0.89/1.12          | (v1_partfun1 @ X30 @ (k1_relat_1 @ X30)))),
% 0.89/1.12      inference('simplify', [status(thm)], ['9'])).
% 0.89/1.12  thf('11', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['8', '10'])).
% 0.89/1.12  thf('12', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['11'])).
% 0.89/1.12  thf('13', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['5', '12'])).
% 0.89/1.12  thf('14', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['4', '13'])).
% 0.89/1.12  thf('15', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.12  thf('16', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['3', '15'])).
% 0.89/1.12  thf('17', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['16'])).
% 0.89/1.12  thf('18', plain,
% 0.89/1.12      (![X5 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X5)
% 0.89/1.12          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.89/1.12          | ~ (v1_funct_1 @ X5)
% 0.89/1.12          | ~ (v1_relat_1 @ X5))),
% 0.89/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.12  thf('19', plain,
% 0.89/1.12      (![X4 : $i]:
% 0.89/1.12         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.89/1.12          | ~ (v1_funct_1 @ X4)
% 0.89/1.12          | ~ (v1_relat_1 @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.12  thf('20', plain,
% 0.89/1.12      (![X4 : $i]:
% 0.89/1.12         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.89/1.12          | ~ (v1_funct_1 @ X4)
% 0.89/1.12          | ~ (v1_relat_1 @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.12  thf('21', plain,
% 0.89/1.12      (![X5 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X5)
% 0.89/1.12          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.89/1.12          | ~ (v1_funct_1 @ X5)
% 0.89/1.12          | ~ (v1_relat_1 @ X5))),
% 0.89/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.12  thf('22', plain,
% 0.89/1.12      (![X31 : $i]:
% 0.89/1.12         ((m1_subset_1 @ X31 @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 0.89/1.12          | ~ (v1_funct_1 @ X31)
% 0.89/1.12          | ~ (v1_relat_1 @ X31))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.12  thf('23', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['21', '22'])).
% 0.89/1.12  thf('24', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_zfmisc_1 @ 
% 0.89/1.12              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.89/1.12               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.12  thf('25', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['24'])).
% 0.89/1.12  thf('26', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_zfmisc_1 @ 
% 0.89/1.12              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.89/1.12               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['19', '25'])).
% 0.89/1.12  thf('27', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['26'])).
% 0.89/1.12  thf('28', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['18', '27'])).
% 0.89/1.12  thf('29', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_zfmisc_1 @ 
% 0.89/1.12              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.89/1.12      inference('simplify', [status(thm)], ['28'])).
% 0.89/1.12  thf(cc2_partfun1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.89/1.12       ( ![C:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.12           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.89/1.12  thf('30', plain,
% 0.89/1.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.89/1.12         ((v1_xboole_0 @ X15)
% 0.89/1.12          | ~ (v1_xboole_0 @ X16)
% 0.89/1.12          | ~ (v1_partfun1 @ X17 @ X15)
% 0.89/1.12          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.89/1.12  thf('31', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.89/1.12          | (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.12  thf('32', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['17', '31'])).
% 0.89/1.12  thf('33', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.89/1.12          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['32'])).
% 0.89/1.12  thf('34', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['2', '33'])).
% 0.89/1.12  thf(t62_tops_2, conjecture,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_struct_0 @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.89/1.12           ( ![C:$i]:
% 0.89/1.12             ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.12                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.12                 ( m1_subset_1 @
% 0.89/1.12                   C @ 
% 0.89/1.12                   ( k1_zfmisc_1 @
% 0.89/1.12                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.12               ( ( ( ( k2_relset_1 @
% 0.89/1.12                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.89/1.12                     ( k2_struct_0 @ B ) ) & 
% 0.89/1.12                   ( v2_funct_1 @ C ) ) =>
% 0.89/1.12                 ( ( ( k1_relset_1 @
% 0.89/1.12                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.12                       ( k2_tops_2 @
% 0.89/1.12                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.12                     ( k2_struct_0 @ B ) ) & 
% 0.89/1.12                   ( ( k2_relset_1 @
% 0.89/1.12                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.12                       ( k2_tops_2 @
% 0.89/1.12                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.12                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.89/1.12  thf(zf_stmt_1, negated_conjecture,
% 0.89/1.12    (~( ![A:$i]:
% 0.89/1.12        ( ( l1_struct_0 @ A ) =>
% 0.89/1.12          ( ![B:$i]:
% 0.89/1.12            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.89/1.12              ( ![C:$i]:
% 0.89/1.12                ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.12                    ( v1_funct_2 @
% 0.89/1.12                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.12                    ( m1_subset_1 @
% 0.89/1.12                      C @ 
% 0.89/1.12                      ( k1_zfmisc_1 @
% 0.89/1.12                        ( k2_zfmisc_1 @
% 0.89/1.12                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.12                  ( ( ( ( k2_relset_1 @
% 0.89/1.12                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.89/1.12                        ( k2_struct_0 @ B ) ) & 
% 0.89/1.12                      ( v2_funct_1 @ C ) ) =>
% 0.89/1.12                    ( ( ( k1_relset_1 @
% 0.89/1.12                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.12                          ( k2_tops_2 @
% 0.89/1.12                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.12                        ( k2_struct_0 @ B ) ) & 
% 0.89/1.12                      ( ( k2_relset_1 @
% 0.89/1.12                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.12                          ( k2_tops_2 @
% 0.89/1.12                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.12                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.89/1.12    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.89/1.12  thf('35', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.12       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.12  thf('36', plain,
% 0.89/1.12      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.12         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.89/1.12          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.89/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.12  thf('37', plain,
% 0.89/1.12      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.12         = (k2_relat_1 @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('38', plain,
% 0.89/1.12      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.12         = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf(fc5_struct_0, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.89/1.12       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.89/1.12  thf('40', plain,
% 0.89/1.12      (![X33 : $i]:
% 0.89/1.12         (~ (v1_xboole_0 @ (k2_struct_0 @ X33))
% 0.89/1.12          | ~ (l1_struct_0 @ X33)
% 0.89/1.12          | (v2_struct_0 @ X33))),
% 0.89/1.12      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.89/1.12  thf('41', plain,
% 0.89/1.12      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.89/1.12        | (v2_struct_0 @ sk_B)
% 0.89/1.12        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.12  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('43', plain,
% 0.89/1.12      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.89/1.12      inference('demod', [status(thm)], ['41', '42'])).
% 0.89/1.12  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('45', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.89/1.12      inference('clc', [status(thm)], ['43', '44'])).
% 0.89/1.12  thf('46', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ sk_C)
% 0.89/1.12          | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12          | ~ (v1_relat_1 @ sk_C)
% 0.89/1.12          | (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['34', '45'])).
% 0.89/1.12  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('49', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf(cc2_relat_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( v1_relat_1 @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.89/1.12  thf('50', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.89/1.12          | (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X1))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.12  thf('51', plain,
% 0.89/1.12      ((~ (v1_relat_1 @ 
% 0.89/1.12           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.89/1.12        | (v1_relat_1 @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['49', '50'])).
% 0.89/1.12  thf(fc6_relat_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.12  thf('52', plain,
% 0.89/1.12      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.89/1.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.12  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('54', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 0.89/1.12      inference('demod', [status(thm)], ['46', '47', '48', '53'])).
% 0.89/1.12  thf('55', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_zfmisc_1 @ 
% 0.89/1.12              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.89/1.12      inference('simplify', [status(thm)], ['28'])).
% 0.89/1.12  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.89/1.12  thf(zf_stmt_3, axiom,
% 0.89/1.12    (![C:$i,B:$i,A:$i]:
% 0.89/1.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.89/1.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.12  thf(zf_stmt_5, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.89/1.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.89/1.12  thf('56', plain,
% 0.89/1.12      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.12         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.89/1.12          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.89/1.12          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.12  thf('57', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | (zip_tseitin_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.89/1.12             (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (zip_tseitin_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['55', '56'])).
% 0.89/1.12  thf('58', plain,
% 0.89/1.12      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12         (k2_relat_1 @ sk_C))
% 0.89/1.12        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['54', '57'])).
% 0.89/1.12  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('62', plain,
% 0.89/1.12      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12        (k2_relat_1 @ sk_C))),
% 0.89/1.12      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.89/1.12  thf('63', plain,
% 0.89/1.12      (![X5 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X5)
% 0.89/1.12          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.89/1.12          | ~ (v1_funct_1 @ X5)
% 0.89/1.12          | ~ (v1_relat_1 @ X5))),
% 0.89/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.12  thf('64', plain,
% 0.89/1.12      (![X4 : $i]:
% 0.89/1.12         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.89/1.12          | ~ (v1_funct_1 @ X4)
% 0.89/1.12          | ~ (v1_relat_1 @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.12  thf('65', plain,
% 0.89/1.12      (![X4 : $i]:
% 0.89/1.12         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.89/1.12          | ~ (v1_funct_1 @ X4)
% 0.89/1.12          | ~ (v1_relat_1 @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.12  thf('66', plain,
% 0.89/1.12      (![X5 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X5)
% 0.89/1.12          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.89/1.12          | ~ (v1_funct_1 @ X5)
% 0.89/1.12          | ~ (v1_relat_1 @ X5))),
% 0.89/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.12  thf('67', plain,
% 0.89/1.12      (![X31 : $i]:
% 0.89/1.12         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 0.89/1.12          | ~ (v1_funct_1 @ X31)
% 0.89/1.12          | ~ (v1_relat_1 @ X31))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.12  thf('68', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.12           (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['66', '67'])).
% 0.89/1.12  thf('69', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['65', '68'])).
% 0.89/1.12  thf('70', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.12           (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['69'])).
% 0.89/1.12  thf('71', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['64', '70'])).
% 0.89/1.12  thf('72', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.89/1.12           (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['71'])).
% 0.89/1.12  thf('73', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.89/1.12           (k1_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['63', '72'])).
% 0.89/1.12  thf('74', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.89/1.12             (k1_relat_1 @ X0)))),
% 0.89/1.12      inference('simplify', [status(thm)], ['73'])).
% 0.89/1.12  thf('75', plain,
% 0.89/1.12      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.12         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.89/1.12          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.89/1.12          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.12  thf('76', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (zip_tseitin_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.89/1.12               (k2_relat_1 @ X0))
% 0.89/1.12          | ((k2_relat_1 @ X0)
% 0.89/1.12              = (k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.89/1.12                 (k2_funct_1 @ X0))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['74', '75'])).
% 0.89/1.12  thf('77', plain,
% 0.89/1.12      ((((k2_relat_1 @ sk_C)
% 0.89/1.12          = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12             (k2_funct_1 @ sk_C)))
% 0.89/1.12        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['62', '76'])).
% 0.89/1.12  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('81', plain,
% 0.89/1.12      (((k2_relat_1 @ sk_C)
% 0.89/1.12         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12            (k2_funct_1 @ sk_C)))),
% 0.89/1.12      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.89/1.12  thf(d3_struct_0, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.89/1.12  thf('82', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('84', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('85', plain,
% 0.89/1.12      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_B))
% 0.89/1.12        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12            != (k2_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('86', plain,
% 0.89/1.12      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('split', [status(esa)], ['85'])).
% 0.89/1.12  thf('87', plain,
% 0.89/1.12      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12           != (k2_struct_0 @ sk_B))
% 0.89/1.12         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['84', '86'])).
% 0.89/1.12  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('89', plain,
% 0.89/1.12      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('demod', [status(thm)], ['87', '88'])).
% 0.89/1.12  thf('90', plain,
% 0.89/1.12      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['83', '89'])).
% 0.89/1.12  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('92', plain,
% 0.89/1.12      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('demod', [status(thm)], ['90', '91'])).
% 0.89/1.12  thf('93', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('94', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('95', plain,
% 0.89/1.12      (((m1_subset_1 @ sk_C @ 
% 0.89/1.12         (k1_zfmisc_1 @ 
% 0.89/1.12          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.89/1.12        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['93', '94'])).
% 0.89/1.12  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('97', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('demod', [status(thm)], ['95', '96'])).
% 0.89/1.12  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('99', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.12      inference('demod', [status(thm)], ['97', '98'])).
% 0.89/1.12  thf(cc5_funct_2, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.89/1.12       ( ![C:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.12           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.89/1.12             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.89/1.12  thf('100', plain,
% 0.89/1.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.89/1.12          | (v1_partfun1 @ X18 @ X19)
% 0.89/1.12          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.89/1.12          | ~ (v1_funct_1 @ X18)
% 0.89/1.12          | (v1_xboole_0 @ X20))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.89/1.12  thf('101', plain,
% 0.89/1.12      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.89/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.89/1.12        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['99', '100'])).
% 0.89/1.12  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('103', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('104', plain,
% 0.89/1.12      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('105', plain,
% 0.89/1.12      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.89/1.12        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['103', '104'])).
% 0.89/1.12  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('107', plain,
% 0.89/1.12      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('demod', [status(thm)], ['105', '106'])).
% 0.89/1.12  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('109', plain,
% 0.89/1.12      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.89/1.12      inference('demod', [status(thm)], ['107', '108'])).
% 0.89/1.12  thf('110', plain,
% 0.89/1.12      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.89/1.12        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('demod', [status(thm)], ['101', '102', '109'])).
% 0.89/1.12  thf('111', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.89/1.12      inference('clc', [status(thm)], ['43', '44'])).
% 0.89/1.12  thf('112', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.89/1.12      inference('clc', [status(thm)], ['110', '111'])).
% 0.89/1.12  thf('113', plain,
% 0.89/1.12      (![X29 : $i, X30 : $i]:
% 0.89/1.12         (~ (v1_partfun1 @ X30 @ X29)
% 0.89/1.12          | ((k1_relat_1 @ X30) = (X29))
% 0.89/1.12          | ~ (v4_relat_1 @ X30 @ X29)
% 0.89/1.12          | ~ (v1_relat_1 @ X30))),
% 0.89/1.12      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.89/1.12  thf('114', plain,
% 0.89/1.12      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.12        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.89/1.12        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['112', '113'])).
% 0.89/1.12  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('116', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('117', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((v4_relat_1 @ X9 @ X10)
% 0.89/1.12          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.12  thf('118', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['116', '117'])).
% 0.89/1.12  thf('119', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['114', '115', '118'])).
% 0.89/1.12  thf('120', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['114', '115', '118'])).
% 0.89/1.12  thf('121', plain,
% 0.89/1.12      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_B))))),
% 0.89/1.12      inference('demod', [status(thm)], ['92', '119', '120'])).
% 0.89/1.12  thf('122', plain,
% 0.89/1.12      (![X5 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X5)
% 0.89/1.12          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.89/1.12          | ~ (v1_funct_1 @ X5)
% 0.89/1.12          | ~ (v1_relat_1 @ X5))),
% 0.89/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.12  thf('123', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.89/1.12             (k1_zfmisc_1 @ 
% 0.89/1.12              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.89/1.12      inference('simplify', [status(thm)], ['28'])).
% 0.89/1.12  thf('124', plain,
% 0.89/1.12      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.12         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.89/1.12          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.89/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.12  thf('125', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.89/1.12              (k2_funct_1 @ X0)) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['123', '124'])).
% 0.89/1.12  thf('126', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('127', plain,
% 0.89/1.12      (![X31 : $i]:
% 0.89/1.12         ((m1_subset_1 @ X31 @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 0.89/1.12          | ~ (v1_funct_1 @ X31)
% 0.89/1.12          | ~ (v1_relat_1 @ X31))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.12  thf('128', plain,
% 0.89/1.12      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.12         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.89/1.12          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.89/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.12  thf('129', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['127', '128'])).
% 0.89/1.12  thf('130', plain,
% 0.89/1.12      (![X31 : $i]:
% 0.89/1.12         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 0.89/1.12          | ~ (v1_funct_1 @ X31)
% 0.89/1.12          | ~ (v1_relat_1 @ X31))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.12  thf('131', plain,
% 0.89/1.12      (![X31 : $i]:
% 0.89/1.12         ((m1_subset_1 @ X31 @ 
% 0.89/1.12           (k1_zfmisc_1 @ 
% 0.89/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 0.89/1.12          | ~ (v1_funct_1 @ X31)
% 0.89/1.12          | ~ (v1_relat_1 @ X31))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.12  thf(d4_tops_2, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.12       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.89/1.12         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.89/1.12  thf('132', plain,
% 0.89/1.12      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.89/1.12         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.89/1.12          | ~ (v2_funct_1 @ X36)
% 0.89/1.12          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.89/1.12          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.89/1.12          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.89/1.12          | ~ (v1_funct_1 @ X36))),
% 0.89/1.12      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.89/1.12  thf('133', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.12          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              != (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['131', '132'])).
% 0.89/1.12  thf('134', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12            != (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['133'])).
% 0.89/1.12  thf('135', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              != (k2_relat_1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['130', '134'])).
% 0.89/1.12  thf('136', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12            != (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0)
% 0.89/1.12          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['135'])).
% 0.89/1.12  thf('137', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0)
% 0.89/1.12          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v2_funct_1 @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['129', '136'])).
% 0.89/1.12  thf('138', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_funct_1 @ X0)
% 0.89/1.12          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.12              = (k2_funct_1 @ X0))
% 0.89/1.12          | ~ (v1_relat_1 @ X0)
% 0.89/1.12          | ~ (v1_funct_1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['137'])).
% 0.89/1.12  thf('139', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('140', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('141', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('142', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('143', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('split', [status(esa)], ['85'])).
% 0.89/1.12  thf('144', plain,
% 0.89/1.12      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12           != (k2_struct_0 @ sk_A))
% 0.89/1.12         | ~ (l1_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['142', '143'])).
% 0.89/1.12  thf('145', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('146', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['144', '145'])).
% 0.89/1.12  thf('147', plain,
% 0.89/1.12      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12           != (k2_struct_0 @ sk_A))
% 0.89/1.12         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['141', '146'])).
% 0.89/1.12  thf('148', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('149', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['147', '148'])).
% 0.89/1.12  thf('150', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['140', '149'])).
% 0.89/1.12  thf('151', plain,
% 0.89/1.12      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.12           != (k2_struct_0 @ sk_A))
% 0.89/1.12         | ~ (l1_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['139', '150'])).
% 0.89/1.12  thf('152', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('153', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.12          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.12          != (k2_struct_0 @ sk_A)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['151', '152'])).
% 0.89/1.12  thf('154', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('155', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.89/1.12      inference('clc', [status(thm)], ['110', '111'])).
% 0.89/1.12  thf('156', plain,
% 0.89/1.12      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.12      inference('sup+', [status(thm)], ['154', '155'])).
% 0.89/1.12  thf('157', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('158', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['156', '157'])).
% 0.89/1.12  thf('159', plain,
% 0.89/1.12      (![X29 : $i, X30 : $i]:
% 0.89/1.12         (~ (v1_partfun1 @ X30 @ X29)
% 0.89/1.12          | ((k1_relat_1 @ X30) = (X29))
% 0.89/1.12          | ~ (v4_relat_1 @ X30 @ X29)
% 0.89/1.12          | ~ (v1_relat_1 @ X30))),
% 0.89/1.12      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.89/1.12  thf('160', plain,
% 0.89/1.12      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.12        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.89/1.12        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['158', '159'])).
% 0.89/1.12  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('162', plain,
% 0.89/1.12      (![X32 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('163', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('164', plain,
% 0.89/1.12      (((m1_subset_1 @ sk_C @ 
% 0.89/1.12         (k1_zfmisc_1 @ 
% 0.89/1.12          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.89/1.12        | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.12      inference('sup+', [status(thm)], ['162', '163'])).
% 0.89/1.12  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('166', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_C @ 
% 0.89/1.12        (k1_zfmisc_1 @ 
% 0.89/1.12         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.12      inference('demod', [status(thm)], ['164', '165'])).
% 0.89/1.12  thf('167', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((v4_relat_1 @ X9 @ X10)
% 0.89/1.12          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.12  thf('168', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['166', '167'])).
% 0.89/1.12  thf('169', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['160', '161', '168'])).
% 0.89/1.12  thf('170', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['160', '161', '168'])).
% 0.89/1.12  thf('171', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.89/1.12      inference('demod', [status(thm)], ['160', '161', '168'])).
% 0.89/1.12  thf('172', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.12          != (k1_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['153', '169', '170', '171'])).
% 0.89/1.12  thf('173', plain,
% 0.89/1.12      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12           (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.89/1.12         | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12         | ~ (v1_relat_1 @ sk_C)
% 0.89/1.12         | ~ (v2_funct_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['138', '172'])).
% 0.89/1.12  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('177', plain,
% 0.89/1.12      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 0.89/1.12  thf('178', plain,
% 0.89/1.12      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12           (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.89/1.12         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['126', '177'])).
% 0.89/1.12  thf('179', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('180', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('181', plain,
% 0.89/1.12      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.12          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.89/1.12  thf('182', plain,
% 0.89/1.12      (((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.89/1.12         | ~ (v2_funct_1 @ sk_C)
% 0.89/1.12         | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12         | ~ (v1_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['125', '181'])).
% 0.89/1.12  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('186', plain,
% 0.89/1.12      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 0.89/1.12  thf('187', plain,
% 0.89/1.12      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.89/1.12         | ~ (v1_relat_1 @ sk_C)
% 0.89/1.12         | ~ (v1_funct_1 @ sk_C)
% 0.89/1.12         | ~ (v2_funct_1 @ sk_C)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.12                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.12                = (k2_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['122', '186'])).
% 0.89/1.12  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.12  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.12  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('191', plain,
% 0.89/1.13      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.89/1.13         <= (~
% 0.89/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13                = (k2_struct_0 @ sk_A))))),
% 0.89/1.13      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.89/1.13  thf('192', plain,
% 0.89/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13          = (k2_struct_0 @ sk_A)))),
% 0.89/1.13      inference('simplify', [status(thm)], ['191'])).
% 0.89/1.13  thf('193', plain,
% 0.89/1.13      (~
% 0.89/1.13       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13          = (k2_struct_0 @ sk_B))) | 
% 0.89/1.13       ~
% 0.89/1.13       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13          = (k2_struct_0 @ sk_A)))),
% 0.89/1.13      inference('split', [status(esa)], ['85'])).
% 0.89/1.13  thf('194', plain,
% 0.89/1.13      (~
% 0.89/1.13       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13          = (k2_struct_0 @ sk_B)))),
% 0.89/1.13      inference('sat_resolution*', [status(thm)], ['192', '193'])).
% 0.89/1.13  thf('195', plain,
% 0.89/1.13      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.13         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13         != (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('simpl_trail', [status(thm)], ['121', '194'])).
% 0.89/1.13  thf('196', plain,
% 0.89/1.13      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.13          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.13          != (k2_relat_1 @ sk_C))
% 0.89/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup-', [status(thm)], ['82', '195'])).
% 0.89/1.13  thf('197', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.13  thf('198', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.13      inference('demod', [status(thm)], ['97', '98'])).
% 0.89/1.13  thf('199', plain,
% 0.89/1.13      (![X32 : $i]:
% 0.89/1.13         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.13  thf('200', plain,
% 0.89/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['107', '108'])).
% 0.89/1.13  thf('201', plain,
% 0.89/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.13         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.89/1.13          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.89/1.13          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.13  thf('202', plain,
% 0.89/1.13      ((~ (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.13        | ((u1_struct_0 @ sk_A)
% 0.89/1.13            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['200', '201'])).
% 0.89/1.13  thf('203', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.13      inference('demod', [status(thm)], ['97', '98'])).
% 0.89/1.13  thf('204', plain,
% 0.89/1.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.13         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.89/1.13          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.89/1.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('205', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.13        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['203', '204'])).
% 0.89/1.13  thf('206', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.89/1.13      inference('sup+', [status(thm)], ['0', '1'])).
% 0.89/1.13  thf('207', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('clc', [status(thm)], ['43', '44'])).
% 0.89/1.13  thf('208', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)),
% 0.89/1.13      inference('sup-', [status(thm)], ['206', '207'])).
% 0.89/1.13  thf('209', plain,
% 0.89/1.13      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['205', '208'])).
% 0.89/1.13  thf('210', plain,
% 0.89/1.13      (((u1_struct_0 @ sk_A)
% 0.89/1.13         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['202', '209'])).
% 0.89/1.13  thf('211', plain,
% 0.89/1.13      ((((u1_struct_0 @ sk_A)
% 0.89/1.13          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.13        | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.13      inference('sup+', [status(thm)], ['199', '210'])).
% 0.89/1.13  thf('212', plain,
% 0.89/1.13      (![X32 : $i]:
% 0.89/1.13         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.13  thf('213', plain,
% 0.89/1.13      (![X32 : $i]:
% 0.89/1.13         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.13  thf('214', plain,
% 0.89/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('215', plain,
% 0.89/1.13      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.89/1.13        | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.13      inference('sup+', [status(thm)], ['213', '214'])).
% 0.89/1.13  thf('216', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('217', plain,
% 0.89/1.13      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['215', '216'])).
% 0.89/1.13  thf('218', plain,
% 0.89/1.13      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.89/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['212', '217'])).
% 0.89/1.13  thf('219', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('220', plain,
% 0.89/1.13      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['218', '219'])).
% 0.89/1.13  thf('221', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.13  thf('222', plain,
% 0.89/1.13      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['220', '221'])).
% 0.89/1.13  thf('223', plain,
% 0.89/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.13         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.89/1.13          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.89/1.13          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.13  thf('224', plain,
% 0.89/1.13      ((~ (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 0.89/1.13        | ((k2_struct_0 @ sk_A)
% 0.89/1.13            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['222', '223'])).
% 0.89/1.13  thf('225', plain,
% 0.89/1.13      (![X32 : $i]:
% 0.89/1.13         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.13  thf('226', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.13      inference('demod', [status(thm)], ['164', '165'])).
% 0.89/1.13  thf('227', plain,
% 0.89/1.13      (((m1_subset_1 @ sk_C @ 
% 0.89/1.13         (k1_zfmisc_1 @ 
% 0.89/1.13          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.89/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['225', '226'])).
% 0.89/1.13  thf('228', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('229', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.89/1.13      inference('demod', [status(thm)], ['227', '228'])).
% 0.89/1.13  thf('230', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.13  thf('231', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.13      inference('demod', [status(thm)], ['229', '230'])).
% 0.89/1.13  thf('232', plain,
% 0.89/1.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.13         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.89/1.13          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.89/1.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('233', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))
% 0.89/1.13        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['231', '232'])).
% 0.89/1.13  thf('234', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)),
% 0.89/1.13      inference('sup-', [status(thm)], ['206', '207'])).
% 0.89/1.13  thf('235', plain,
% 0.89/1.13      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['233', '234'])).
% 0.89/1.13  thf('236', plain,
% 0.89/1.13      (((k2_struct_0 @ sk_A)
% 0.89/1.13         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['224', '235'])).
% 0.89/1.13  thf('237', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('238', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['211', '236', '237'])).
% 0.89/1.13  thf('239', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.13      inference('demod', [status(thm)], ['198', '238'])).
% 0.89/1.13  thf('240', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['160', '161', '168'])).
% 0.89/1.13  thf('241', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ 
% 0.89/1.13        (k1_zfmisc_1 @ 
% 0.89/1.13         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.13      inference('demod', [status(thm)], ['239', '240'])).
% 0.89/1.13  thf('242', plain,
% 0.89/1.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.89/1.13          | ~ (v2_funct_1 @ X36)
% 0.89/1.13          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.89/1.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.89/1.13          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.89/1.13          | ~ (v1_funct_1 @ X36))),
% 0.89/1.13      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.89/1.13  thf('243', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.89/1.13        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13            = (k2_funct_1 @ sk_C))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.13        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13            != (k2_relat_1 @ sk_C)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['241', '242'])).
% 0.89/1.13  thf('244', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('245', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)),
% 0.89/1.13      inference('sup-', [status(thm)], ['206', '207'])).
% 0.89/1.13  thf('246', plain,
% 0.89/1.13      (![X31 : $i]:
% 0.89/1.13         ((m1_subset_1 @ X31 @ 
% 0.89/1.13           (k1_zfmisc_1 @ 
% 0.89/1.13            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 0.89/1.13          | ~ (v1_funct_1 @ X31)
% 0.89/1.13          | ~ (v1_relat_1 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.13  thf('247', plain,
% 0.89/1.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.13         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.89/1.13          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.89/1.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('248', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.89/1.13          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['246', '247'])).
% 0.89/1.13  thf('249', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['245', '248'])).
% 0.89/1.13  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('251', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('252', plain,
% 0.89/1.13      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['249', '250', '251'])).
% 0.89/1.13  thf('253', plain,
% 0.89/1.13      (![X31 : $i]:
% 0.89/1.13         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 0.89/1.13          | ~ (v1_funct_1 @ X31)
% 0.89/1.13          | ~ (v1_relat_1 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.89/1.13  thf('254', plain,
% 0.89/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.13         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.89/1.13          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.89/1.13          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.13  thf('255', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.89/1.13          | ((k1_relat_1 @ X0)
% 0.89/1.13              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['253', '254'])).
% 0.89/1.13  thf('256', plain,
% 0.89/1.13      ((((k1_relat_1 @ sk_C)
% 0.89/1.13          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['252', '255'])).
% 0.89/1.13  thf('257', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('258', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('demod', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('259', plain,
% 0.89/1.13      (((k1_relat_1 @ sk_C)
% 0.89/1.13         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['256', '257', '258'])).
% 0.89/1.13  thf('260', plain,
% 0.89/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.13         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 0.89/1.13          | (v1_funct_2 @ X25 @ X23 @ X24)
% 0.89/1.13          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.13  thf('261', plain,
% 0.89/1.13      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.89/1.13        | ~ (zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.89/1.13        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['259', '260'])).
% 0.89/1.13  thf('262', plain,
% 0.89/1.13      ((zip_tseitin_1 @ sk_C @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['249', '250', '251'])).
% 0.89/1.13  thf('263', plain,
% 0.89/1.13      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.89/1.13        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['261', '262'])).
% 0.89/1.13  thf('264', plain,
% 0.89/1.13      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['263'])).
% 0.89/1.13  thf('265', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('266', plain,
% 0.89/1.13      (![X32 : $i]:
% 0.89/1.13         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.89/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.13  thf('267', plain,
% 0.89/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.13         = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('268', plain,
% 0.89/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.89/1.13          = (k2_struct_0 @ sk_B))
% 0.89/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['266', '267'])).
% 0.89/1.13  thf('269', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('270', plain,
% 0.89/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.89/1.13         = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['268', '269'])).
% 0.89/1.13  thf('271', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.13  thf('272', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.13  thf('273', plain,
% 0.89/1.13      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13         = (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['270', '271', '272'])).
% 0.89/1.13  thf('274', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['211', '236', '237'])).
% 0.89/1.13  thf('275', plain,
% 0.89/1.13      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13         = (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['273', '274'])).
% 0.89/1.13  thf('276', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['160', '161', '168'])).
% 0.89/1.13  thf('277', plain,
% 0.89/1.13      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13         = (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['275', '276'])).
% 0.89/1.13  thf('278', plain,
% 0.89/1.13      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13          = (k2_funct_1 @ sk_C))
% 0.89/1.13        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)], ['243', '244', '264', '265', '277'])).
% 0.89/1.13  thf('279', plain,
% 0.89/1.13      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.13         = (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['278'])).
% 0.89/1.13  thf('280', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.13  thf('281', plain,
% 0.89/1.13      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.89/1.13         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['196', '197', '279', '280'])).
% 0.89/1.13  thf('282', plain, ($false),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['81', '281'])).
% 0.89/1.13  
% 0.89/1.13  % SZS output end Refutation
% 0.89/1.13  
% 0.89/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
