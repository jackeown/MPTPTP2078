%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xWYhnBNxHU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:48 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  333 (85164 expanded)
%              Number of leaves         :   45 (24225 expanded)
%              Depth                    :   38
%              Number of atoms          : 2850 (2153189 expanded)
%              Number of equality atoms :  196 (108771 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('29',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','37'])).

thf('39',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','50'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X29 @ X30 @ X31 ) @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','61'])).

thf('63',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','50'])).

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

thf('65',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('72',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','74'])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','80'])).

thf('82',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','50'])).

thf('85',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X29 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

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

thf('92',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','93'])).

thf('95',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','80'])).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['99'])).

thf('101',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','37'])).

thf('102',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('107',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','107'])).

thf('110',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('112',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','108','109','110','111'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('115',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('119',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['99'])).

thf('121',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('126',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','107'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('131',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('133',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('145',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('149',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['153','158'])).

thf('160',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('164',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','142','151','152','166'])).

thf('168',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','168','169'])).

thf('171',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','170'])).

thf('172',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['99'])).

thf('179',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['177','178'])).

thf('180',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','179'])).

thf('181',plain,
    ( ( ( u1_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','180'])).

thf('182',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','181'])).

thf('183',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('184',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['81','186'])).

thf('188',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('189',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('190',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('192',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','50'])).

thf('193',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X29 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('194',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('197',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['191','197'])).

thf('199',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('200',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('203',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','80'])).

thf('205',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','203','204'])).

thf('206',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('207',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('209',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('210',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('212',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('213',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('215',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('216',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('217',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('219',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('222',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != X22 )
      | ( v1_partfun1 @ X23 @ X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('223',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v4_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
      | ( v1_partfun1 @ X23 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['221','223'])).

thf('225',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['220','224'])).

thf('226',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('230',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['225','226','227','228','229'])).

thf('231',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['214','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('237',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('239',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('240',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','210','213','240'])).

thf('242',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['185'])).

thf('243',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('245',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('246',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['244','247'])).

thf('249',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('252',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['248','249','250','251'])).

thf('253',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('254',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['185'])).

thf('256',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','257'])).

thf('259',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('260',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['256'])).

thf('261',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['258','261'])).

thf('263',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['187','262'])).

thf('264',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('265',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','179'])).

thf('267',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['185'])).

thf('268',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['258','261'])).

thf('270',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['256'])).

thf('271',plain,(
    ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,(
    ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['265','271'])).

thf('273',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('274',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['185'])).

thf('275',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['258','261'])).

thf('277',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('279',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('281',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('282',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['280','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['283'])).

thf('285',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['279','284'])).

thf('286',plain,(
    $false ),
    inference(demod,[status(thm)],['272','285'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xWYhnBNxHU
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.52/1.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.52/1.75  % Solved by: fo/fo7.sh
% 1.52/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.75  % done 883 iterations in 1.298s
% 1.52/1.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.52/1.75  % SZS output start Refutation
% 1.52/1.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.52/1.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.52/1.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.52/1.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.52/1.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.52/1.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.52/1.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.52/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.52/1.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.52/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.52/1.75  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.52/1.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.52/1.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.52/1.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.52/1.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.52/1.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.52/1.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.52/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.52/1.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.52/1.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.52/1.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.52/1.75  thf(sk_C_type, type, sk_C: $i).
% 1.52/1.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.52/1.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.52/1.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.52/1.75  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.52/1.75  thf(d3_struct_0, axiom,
% 1.52/1.75    (![A:$i]:
% 1.52/1.75     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.52/1.75  thf('0', plain,
% 1.52/1.75      (![X24 : $i]:
% 1.52/1.75         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.75  thf(t62_tops_2, conjecture,
% 1.52/1.75    (![A:$i]:
% 1.52/1.75     ( ( l1_struct_0 @ A ) =>
% 1.52/1.75       ( ![B:$i]:
% 1.52/1.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.52/1.75           ( ![C:$i]:
% 1.52/1.75             ( ( ( v1_funct_1 @ C ) & 
% 1.52/1.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.52/1.75                 ( m1_subset_1 @
% 1.52/1.75                   C @ 
% 1.52/1.75                   ( k1_zfmisc_1 @
% 1.52/1.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.52/1.75               ( ( ( ( k2_relset_1 @
% 1.52/1.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.52/1.75                     ( k2_struct_0 @ B ) ) & 
% 1.52/1.75                   ( v2_funct_1 @ C ) ) =>
% 1.52/1.75                 ( ( ( k1_relset_1 @
% 1.52/1.75                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.52/1.75                       ( k2_tops_2 @
% 1.52/1.75                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.52/1.75                     ( k2_struct_0 @ B ) ) & 
% 1.52/1.75                   ( ( k2_relset_1 @
% 1.52/1.75                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.52/1.75                       ( k2_tops_2 @
% 1.52/1.75                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.52/1.75                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.52/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.75    (~( ![A:$i]:
% 1.52/1.75        ( ( l1_struct_0 @ A ) =>
% 1.52/1.75          ( ![B:$i]:
% 1.52/1.75            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.52/1.75              ( ![C:$i]:
% 1.52/1.75                ( ( ( v1_funct_1 @ C ) & 
% 1.52/1.75                    ( v1_funct_2 @
% 1.52/1.75                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.52/1.75                    ( m1_subset_1 @
% 1.52/1.75                      C @ 
% 1.52/1.75                      ( k1_zfmisc_1 @
% 1.52/1.75                        ( k2_zfmisc_1 @
% 1.52/1.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.52/1.75                  ( ( ( ( k2_relset_1 @
% 1.52/1.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.52/1.75                        ( k2_struct_0 @ B ) ) & 
% 1.52/1.75                      ( v2_funct_1 @ C ) ) =>
% 1.52/1.75                    ( ( ( k1_relset_1 @
% 1.52/1.75                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.52/1.75                          ( k2_tops_2 @
% 1.52/1.75                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.52/1.75                        ( k2_struct_0 @ B ) ) & 
% 1.52/1.75                      ( ( k2_relset_1 @
% 1.52/1.75                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.52/1.75                          ( k2_tops_2 @
% 1.52/1.75                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.52/1.75                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.52/1.75    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.52/1.75  thf('1', plain,
% 1.52/1.75      ((m1_subset_1 @ sk_C @ 
% 1.52/1.75        (k1_zfmisc_1 @ 
% 1.52/1.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('2', plain,
% 1.52/1.75      (((m1_subset_1 @ sk_C @ 
% 1.52/1.75         (k1_zfmisc_1 @ 
% 1.52/1.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.52/1.75        | ~ (l1_struct_0 @ sk_A))),
% 1.52/1.75      inference('sup+', [status(thm)], ['0', '1'])).
% 1.52/1.75  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('4', plain,
% 1.52/1.75      ((m1_subset_1 @ sk_C @ 
% 1.52/1.75        (k1_zfmisc_1 @ 
% 1.52/1.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.75      inference('demod', [status(thm)], ['2', '3'])).
% 1.52/1.75  thf('5', plain,
% 1.52/1.75      (![X24 : $i]:
% 1.52/1.75         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.75  thf('6', plain,
% 1.52/1.75      (![X24 : $i]:
% 1.52/1.75         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.75  thf('7', plain,
% 1.52/1.75      ((m1_subset_1 @ sk_C @ 
% 1.52/1.75        (k1_zfmisc_1 @ 
% 1.52/1.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('8', plain,
% 1.52/1.75      (((m1_subset_1 @ sk_C @ 
% 1.52/1.75         (k1_zfmisc_1 @ 
% 1.52/1.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.52/1.75        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.75      inference('sup+', [status(thm)], ['6', '7'])).
% 1.52/1.75  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('10', plain,
% 1.52/1.75      ((m1_subset_1 @ sk_C @ 
% 1.52/1.75        (k1_zfmisc_1 @ 
% 1.52/1.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.52/1.75      inference('demod', [status(thm)], ['8', '9'])).
% 1.52/1.75  thf('11', plain,
% 1.52/1.75      ((m1_subset_1 @ sk_C @ 
% 1.52/1.75        (k1_zfmisc_1 @ 
% 1.52/1.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf(redefinition_k2_relset_1, axiom,
% 1.52/1.75    (![A:$i,B:$i,C:$i]:
% 1.52/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.52/1.75  thf('12', plain,
% 1.52/1.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.52/1.75         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.52/1.75          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.52/1.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.52/1.75  thf('13', plain,
% 1.52/1.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.75         = (k2_relat_1 @ sk_C))),
% 1.52/1.75      inference('sup-', [status(thm)], ['11', '12'])).
% 1.52/1.75  thf('14', plain,
% 1.52/1.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.75         = (k2_struct_0 @ sk_B))),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('16', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['10', '15'])).
% 1.52/1.76  thf(cc5_funct_2, axiom,
% 1.52/1.76    (![A:$i,B:$i]:
% 1.52/1.76     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.52/1.76       ( ![C:$i]:
% 1.52/1.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.76           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.52/1.76             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.52/1.76  thf('17', plain,
% 1.52/1.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.52/1.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.52/1.76          | (v1_partfun1 @ X11 @ X12)
% 1.52/1.76          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 1.52/1.76          | ~ (v1_funct_1 @ X11)
% 1.52/1.76          | (v1_xboole_0 @ X13))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.52/1.76  thf('18', plain,
% 1.52/1.76      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['16', '17'])).
% 1.52/1.76  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('20', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('21', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('22', plain,
% 1.52/1.76      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['20', '21'])).
% 1.52/1.76  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('24', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['22', '23'])).
% 1.52/1.76  thf('25', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('26', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['24', '25'])).
% 1.52/1.76  thf('27', plain,
% 1.52/1.76      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.52/1.76      inference('demod', [status(thm)], ['18', '19', '26'])).
% 1.52/1.76  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('29', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf(fc2_struct_0, axiom,
% 1.52/1.76    (![A:$i]:
% 1.52/1.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.52/1.76       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.52/1.76  thf('30', plain,
% 1.52/1.76      (![X25 : $i]:
% 1.52/1.76         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 1.52/1.76          | ~ (l1_struct_0 @ X25)
% 1.52/1.76          | (v2_struct_0 @ X25))),
% 1.52/1.76      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.52/1.76  thf('31', plain,
% 1.52/1.76      (![X0 : $i]:
% 1.52/1.76         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.52/1.76          | ~ (l1_struct_0 @ X0)
% 1.52/1.76          | (v2_struct_0 @ X0)
% 1.52/1.76          | ~ (l1_struct_0 @ X0))),
% 1.52/1.76      inference('sup-', [status(thm)], ['29', '30'])).
% 1.52/1.76  thf('32', plain,
% 1.52/1.76      (![X0 : $i]:
% 1.52/1.76         ((v2_struct_0 @ X0)
% 1.52/1.76          | ~ (l1_struct_0 @ X0)
% 1.52/1.76          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.52/1.76      inference('simplify', [status(thm)], ['31'])).
% 1.52/1.76  thf('33', plain,
% 1.52/1.76      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B)
% 1.52/1.76        | (v2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup-', [status(thm)], ['28', '32'])).
% 1.52/1.76  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('35', plain,
% 1.52/1.76      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['33', '34'])).
% 1.52/1.76  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('37', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('clc', [status(thm)], ['35', '36'])).
% 1.52/1.76  thf('38', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.52/1.76      inference('clc', [status(thm)], ['27', '37'])).
% 1.52/1.76  thf('39', plain,
% 1.52/1.76      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.52/1.76      inference('sup+', [status(thm)], ['5', '38'])).
% 1.52/1.76  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('41', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['39', '40'])).
% 1.52/1.76  thf(d4_partfun1, axiom,
% 1.52/1.76    (![A:$i,B:$i]:
% 1.52/1.76     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.52/1.76       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.52/1.76  thf('42', plain,
% 1.52/1.76      (![X22 : $i, X23 : $i]:
% 1.52/1.76         (~ (v1_partfun1 @ X23 @ X22)
% 1.52/1.76          | ((k1_relat_1 @ X23) = (X22))
% 1.52/1.76          | ~ (v4_relat_1 @ X23 @ X22)
% 1.52/1.76          | ~ (v1_relat_1 @ X23))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.52/1.76  thf('43', plain,
% 1.52/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.52/1.76        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.52/1.76        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['41', '42'])).
% 1.52/1.76  thf('44', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf(cc1_relset_1, axiom,
% 1.52/1.76    (![A:$i,B:$i,C:$i]:
% 1.52/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.76       ( v1_relat_1 @ C ) ))).
% 1.52/1.76  thf('45', plain,
% 1.52/1.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.52/1.76         ((v1_relat_1 @ X2)
% 1.52/1.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.52/1.76  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.76      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.76  thf('47', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['2', '3'])).
% 1.52/1.76  thf(cc2_relset_1, axiom,
% 1.52/1.76    (![A:$i,B:$i,C:$i]:
% 1.52/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.52/1.76  thf('48', plain,
% 1.52/1.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.76         ((v4_relat_1 @ X5 @ X6)
% 1.52/1.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.52/1.76  thf('49', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('sup-', [status(thm)], ['47', '48'])).
% 1.52/1.76  thf('50', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('51', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['4', '50'])).
% 1.52/1.76  thf(dt_k2_tops_2, axiom,
% 1.52/1.76    (![A:$i,B:$i,C:$i]:
% 1.52/1.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.76       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.52/1.76         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.52/1.76         ( m1_subset_1 @
% 1.52/1.76           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.52/1.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.52/1.76  thf('52', plain,
% 1.52/1.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.52/1.76         ((v1_funct_2 @ (k2_tops_2 @ X29 @ X30 @ X31) @ X30 @ X29)
% 1.52/1.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.52/1.76          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.52/1.76          | ~ (v1_funct_1 @ X31))),
% 1.52/1.76      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.52/1.76  thf('53', plain,
% 1.52/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.52/1.76        | (v1_funct_2 @ 
% 1.52/1.76           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.52/1.76           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['51', '52'])).
% 1.52/1.76  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('55', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('56', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('57', plain,
% 1.52/1.76      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_A))),
% 1.52/1.76      inference('sup+', [status(thm)], ['55', '56'])).
% 1.52/1.76  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('59', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['57', '58'])).
% 1.52/1.76  thf('60', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('61', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['59', '60'])).
% 1.52/1.76  thf('62', plain,
% 1.52/1.76      ((v1_funct_2 @ 
% 1.52/1.76        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.52/1.76        (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['53', '54', '61'])).
% 1.52/1.76  thf('63', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('64', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['4', '50'])).
% 1.52/1.76  thf(d4_tops_2, axiom,
% 1.52/1.76    (![A:$i,B:$i,C:$i]:
% 1.52/1.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.76       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.52/1.76         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.52/1.76  thf('65', plain,
% 1.52/1.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.52/1.76         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 1.52/1.76          | ~ (v2_funct_1 @ X28)
% 1.52/1.76          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 1.52/1.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 1.52/1.76          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 1.52/1.76          | ~ (v1_funct_1 @ X28))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.52/1.76  thf('66', plain,
% 1.52/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.52/1.76        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76            = (k2_funct_1 @ sk_C))
% 1.52/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.52/1.76        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76            != (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['64', '65'])).
% 1.52/1.76  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('68', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['59', '60'])).
% 1.52/1.76  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('70', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['2', '3'])).
% 1.52/1.76  thf('71', plain,
% 1.52/1.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.52/1.76         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.52/1.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.52/1.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.52/1.76  thf('72', plain,
% 1.52/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('sup-', [status(thm)], ['70', '71'])).
% 1.52/1.76  thf('73', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('74', plain,
% 1.52/1.76      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['72', '73'])).
% 1.52/1.76  thf('75', plain,
% 1.52/1.76      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76          = (k2_funct_1 @ sk_C))
% 1.52/1.76        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('demod', [status(thm)], ['66', '67', '68', '69', '74'])).
% 1.52/1.76  thf('76', plain,
% 1.52/1.76      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B)
% 1.52/1.76        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76            = (k2_funct_1 @ sk_C)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['63', '75'])).
% 1.52/1.76  thf('77', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('79', plain,
% 1.52/1.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.52/1.76        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76            = (k2_funct_1 @ sk_C)))),
% 1.52/1.76      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.52/1.76  thf('80', plain,
% 1.52/1.76      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('simplify', [status(thm)], ['79'])).
% 1.52/1.76  thf('81', plain,
% 1.52/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.76        (k1_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['62', '80'])).
% 1.52/1.76  thf('82', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf(d1_funct_2, axiom,
% 1.52/1.76    (![A:$i,B:$i,C:$i]:
% 1.52/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.52/1.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.52/1.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.52/1.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.52/1.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.52/1.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.52/1.76  thf(zf_stmt_1, axiom,
% 1.52/1.76    (![B:$i,A:$i]:
% 1.52/1.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.52/1.76       ( zip_tseitin_0 @ B @ A ) ))).
% 1.52/1.76  thf('83', plain,
% 1.52/1.76      (![X14 : $i, X15 : $i]:
% 1.52/1.76         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.52/1.76  thf('84', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['4', '50'])).
% 1.52/1.76  thf('85', plain,
% 1.52/1.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.52/1.76         ((m1_subset_1 @ (k2_tops_2 @ X29 @ X30 @ X31) @ 
% 1.52/1.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.52/1.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.52/1.76          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.52/1.76          | ~ (v1_funct_1 @ X31))),
% 1.52/1.76      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.52/1.76  thf('86', plain,
% 1.52/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.52/1.76        | (m1_subset_1 @ 
% 1.52/1.76           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.52/1.76           (k1_zfmisc_1 @ 
% 1.52/1.76            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['84', '85'])).
% 1.52/1.76  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('88', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['59', '60'])).
% 1.52/1.76  thf('89', plain,
% 1.52/1.76      ((m1_subset_1 @ 
% 1.52/1.76        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.52/1.76  thf('90', plain,
% 1.52/1.76      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('simplify', [status(thm)], ['79'])).
% 1.52/1.76  thf('91', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['89', '90'])).
% 1.52/1.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.52/1.76  thf(zf_stmt_3, axiom,
% 1.52/1.76    (![C:$i,B:$i,A:$i]:
% 1.52/1.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.52/1.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.52/1.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.52/1.76  thf(zf_stmt_5, axiom,
% 1.52/1.76    (![A:$i,B:$i,C:$i]:
% 1.52/1.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.52/1.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.52/1.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.52/1.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.52/1.76  thf('92', plain,
% 1.52/1.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.76         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.52/1.76          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.52/1.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.52/1.76  thf('93', plain,
% 1.52/1.76      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76         (u1_struct_0 @ sk_B))
% 1.52/1.76        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['91', '92'])).
% 1.52/1.76  thf('94', plain,
% 1.52/1.76      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.52/1.76        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76           (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['83', '93'])).
% 1.52/1.76  thf('95', plain,
% 1.52/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.76        (k1_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['62', '80'])).
% 1.52/1.76  thf('96', plain,
% 1.52/1.76      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.52/1.76         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.52/1.76          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.52/1.76          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.52/1.76  thf('97', plain,
% 1.52/1.76      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76           (u1_struct_0 @ sk_B))
% 1.52/1.76        | ((u1_struct_0 @ sk_B)
% 1.52/1.76            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76               (k2_funct_1 @ sk_C))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['95', '96'])).
% 1.52/1.76  thf('98', plain,
% 1.52/1.76      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.52/1.76        | ((u1_struct_0 @ sk_B)
% 1.52/1.76            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76               (k2_funct_1 @ sk_C))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['94', '97'])).
% 1.52/1.76  thf('99', plain,
% 1.52/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k2_struct_0 @ sk_B))
% 1.52/1.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76            != (k2_struct_0 @ sk_A)))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('100', plain,
% 1.52/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k2_struct_0 @ sk_B)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_B))))),
% 1.52/1.76      inference('split', [status(esa)], ['99'])).
% 1.52/1.76  thf('101', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.52/1.76      inference('clc', [status(thm)], ['27', '37'])).
% 1.52/1.76  thf('102', plain,
% 1.52/1.76      (![X22 : $i, X23 : $i]:
% 1.52/1.76         (~ (v1_partfun1 @ X23 @ X22)
% 1.52/1.76          | ((k1_relat_1 @ X23) = (X22))
% 1.52/1.76          | ~ (v4_relat_1 @ X23 @ X22)
% 1.52/1.76          | ~ (v1_relat_1 @ X23))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.52/1.76  thf('103', plain,
% 1.52/1.76      ((~ (v1_relat_1 @ sk_C)
% 1.52/1.76        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.52/1.76        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['101', '102'])).
% 1.52/1.76  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.76      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.76  thf('105', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('106', plain,
% 1.52/1.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.76         ((v4_relat_1 @ X5 @ X6)
% 1.52/1.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.52/1.76  thf('107', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.52/1.76      inference('sup-', [status(thm)], ['105', '106'])).
% 1.52/1.76  thf('108', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['103', '104', '107'])).
% 1.52/1.76  thf('109', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['103', '104', '107'])).
% 1.52/1.76  thf('110', plain,
% 1.52/1.76      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('simplify', [status(thm)], ['79'])).
% 1.52/1.76  thf('111', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('112', plain,
% 1.52/1.76      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['100', '108', '109', '110', '111'])).
% 1.52/1.76  thf(t55_funct_1, axiom,
% 1.52/1.76    (![A:$i]:
% 1.52/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.76       ( ( v2_funct_1 @ A ) =>
% 1.52/1.76         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.52/1.76           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.52/1.76  thf('113', plain,
% 1.52/1.76      (![X1 : $i]:
% 1.52/1.76         (~ (v2_funct_1 @ X1)
% 1.52/1.76          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.52/1.76          | ~ (v1_funct_1 @ X1)
% 1.52/1.76          | ~ (v1_relat_1 @ X1))),
% 1.52/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.52/1.76  thf('114', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['89', '90'])).
% 1.52/1.76  thf('115', plain,
% 1.52/1.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.52/1.76         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.52/1.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.52/1.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.52/1.76  thf('116', plain,
% 1.52/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['114', '115'])).
% 1.52/1.76  thf('117', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('119', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('120', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k2_struct_0 @ sk_A)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('split', [status(esa)], ['99'])).
% 1.52/1.76  thf('121', plain,
% 1.52/1.76      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.52/1.76           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76           != (k2_struct_0 @ sk_A))
% 1.52/1.76         | ~ (l1_struct_0 @ sk_A)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['119', '120'])).
% 1.52/1.76  thf('122', plain, ((l1_struct_0 @ sk_A)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('123', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k2_struct_0 @ sk_A)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('demod', [status(thm)], ['121', '122'])).
% 1.52/1.76  thf('124', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k2_struct_0 @ sk_A)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['118', '123'])).
% 1.52/1.76  thf('125', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('126', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k1_relat_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('demod', [status(thm)], ['124', '125'])).
% 1.52/1.76  thf('127', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['103', '104', '107'])).
% 1.52/1.76  thf('128', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          != (k1_relat_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('demod', [status(thm)], ['126', '127'])).
% 1.52/1.76  thf('129', plain,
% 1.52/1.76      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76           != (k1_relat_1 @ sk_C))
% 1.52/1.76         | ~ (l1_struct_0 @ sk_B)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['117', '128'])).
% 1.52/1.76  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('131', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('132', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['2', '3'])).
% 1.52/1.76  thf('133', plain,
% 1.52/1.76      (((m1_subset_1 @ sk_C @ 
% 1.52/1.76         (k1_zfmisc_1 @ 
% 1.52/1.76          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['131', '132'])).
% 1.52/1.76  thf('134', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('135', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['133', '134'])).
% 1.52/1.76  thf('136', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('137', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['135', '136'])).
% 1.52/1.76  thf('138', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('139', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['137', '138'])).
% 1.52/1.76  thf('140', plain,
% 1.52/1.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.52/1.76         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 1.52/1.76          | ~ (v2_funct_1 @ X28)
% 1.52/1.76          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 1.52/1.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 1.52/1.76          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 1.52/1.76          | ~ (v1_funct_1 @ X28))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.52/1.76  thf('141', plain,
% 1.52/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76            = (k2_funct_1 @ sk_C))
% 1.52/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.52/1.76        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76            != (k2_relat_1 @ sk_C)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['139', '140'])).
% 1.52/1.76  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('143', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('144', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['57', '58'])).
% 1.52/1.76  thf('145', plain,
% 1.52/1.76      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['143', '144'])).
% 1.52/1.76  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('147', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['145', '146'])).
% 1.52/1.76  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('149', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['147', '148'])).
% 1.52/1.76  thf('150', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('151', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['149', '150'])).
% 1.52/1.76  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('153', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('154', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('155', plain,
% 1.52/1.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('156', plain,
% 1.52/1.76      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76          = (k2_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_A))),
% 1.52/1.76      inference('sup+', [status(thm)], ['154', '155'])).
% 1.52/1.76  thf('157', plain, ((l1_struct_0 @ sk_A)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('158', plain,
% 1.52/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['156', '157'])).
% 1.52/1.76  thf('159', plain,
% 1.52/1.76      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76          = (k2_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['153', '158'])).
% 1.52/1.76  thf('160', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('161', plain,
% 1.52/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.52/1.76         = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['159', '160'])).
% 1.52/1.76  thf('162', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('163', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('164', plain,
% 1.52/1.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76         = (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['161', '162', '163'])).
% 1.52/1.76  thf('165', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.52/1.76      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.52/1.76  thf('166', plain,
% 1.52/1.76      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76         = (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['164', '165'])).
% 1.52/1.76  thf('167', plain,
% 1.52/1.76      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76          = (k2_funct_1 @ sk_C))
% 1.52/1.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.52/1.76      inference('demod', [status(thm)], ['141', '142', '151', '152', '166'])).
% 1.52/1.76  thf('168', plain,
% 1.52/1.76      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76         = (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('simplify', [status(thm)], ['167'])).
% 1.52/1.76  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('170', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('demod', [status(thm)], ['129', '130', '168', '169'])).
% 1.52/1.76  thf('171', plain,
% 1.52/1.76      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['116', '170'])).
% 1.52/1.76  thf('172', plain,
% 1.52/1.76      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.52/1.76         | ~ (v1_relat_1 @ sk_C)
% 1.52/1.76         | ~ (v1_funct_1 @ sk_C)
% 1.52/1.76         | ~ (v2_funct_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['113', '171'])).
% 1.52/1.76  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.76      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.76  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('176', plain,
% 1.52/1.76      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.52/1.76         <= (~
% 1.52/1.76             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76                = (k2_struct_0 @ sk_A))))),
% 1.52/1.76      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 1.52/1.76  thf('177', plain,
% 1.52/1.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          = (k2_struct_0 @ sk_A)))),
% 1.52/1.76      inference('simplify', [status(thm)], ['176'])).
% 1.52/1.76  thf('178', plain,
% 1.52/1.76      (~
% 1.52/1.76       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          = (k2_struct_0 @ sk_B))) | 
% 1.52/1.76       ~
% 1.52/1.76       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          = (k2_struct_0 @ sk_A)))),
% 1.52/1.76      inference('split', [status(esa)], ['99'])).
% 1.52/1.76  thf('179', plain,
% 1.52/1.76      (~
% 1.52/1.76       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76          = (k2_struct_0 @ sk_B)))),
% 1.52/1.76      inference('sat_resolution*', [status(thm)], ['177', '178'])).
% 1.52/1.76  thf('180', plain,
% 1.52/1.76      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('simpl_trail', [status(thm)], ['112', '179'])).
% 1.52/1.76  thf('181', plain,
% 1.52/1.76      ((((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 1.52/1.76        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['98', '180'])).
% 1.52/1.76  thf('182', plain,
% 1.52/1.76      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B)
% 1.52/1.76        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['82', '181'])).
% 1.52/1.76  thf('183', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('184', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('185', plain,
% 1.52/1.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.52/1.76        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.52/1.76      inference('demod', [status(thm)], ['182', '183', '184'])).
% 1.52/1.76  thf('186', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['185'])).
% 1.52/1.76  thf('187', plain,
% 1.52/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ k1_xboole_0)),
% 1.52/1.76      inference('demod', [status(thm)], ['81', '186'])).
% 1.52/1.76  thf('188', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['89', '90'])).
% 1.52/1.76  thf('189', plain,
% 1.52/1.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.52/1.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.52/1.76          | (v1_partfun1 @ X11 @ X12)
% 1.52/1.76          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 1.52/1.76          | ~ (v1_funct_1 @ X11)
% 1.52/1.76          | (v1_xboole_0 @ X13))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.52/1.76  thf('190', plain,
% 1.52/1.76      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.52/1.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.52/1.76        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.76             (k1_relat_1 @ sk_C))
% 1.52/1.76        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['188', '189'])).
% 1.52/1.76  thf('191', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('192', plain,
% 1.52/1.76      ((m1_subset_1 @ sk_C @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.52/1.76      inference('demod', [status(thm)], ['4', '50'])).
% 1.52/1.76  thf('193', plain,
% 1.52/1.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.52/1.76         ((v1_funct_1 @ (k2_tops_2 @ X29 @ X30 @ X31))
% 1.52/1.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.52/1.76          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.52/1.76          | ~ (v1_funct_1 @ X31))),
% 1.52/1.76      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.52/1.76  thf('194', plain,
% 1.52/1.76      ((~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.52/1.76        | (v1_funct_1 @ 
% 1.52/1.76           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['192', '193'])).
% 1.52/1.76  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('196', plain,
% 1.52/1.76      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('demod', [status(thm)], ['59', '60'])).
% 1.52/1.76  thf('197', plain,
% 1.52/1.76      ((v1_funct_1 @ 
% 1.52/1.76        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['194', '195', '196'])).
% 1.52/1.76  thf('198', plain,
% 1.52/1.76      (((v1_funct_1 @ 
% 1.52/1.76         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['191', '197'])).
% 1.52/1.76  thf('199', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('200', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('201', plain,
% 1.52/1.76      ((v1_funct_1 @ 
% 1.52/1.76        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['198', '199', '200'])).
% 1.52/1.76  thf('202', plain,
% 1.52/1.76      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.52/1.76         = (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('simplify', [status(thm)], ['167'])).
% 1.52/1.76  thf('203', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['201', '202'])).
% 1.52/1.76  thf('204', plain,
% 1.52/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.76        (k1_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['62', '80'])).
% 1.52/1.76  thf('205', plain,
% 1.52/1.76      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.52/1.76        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('demod', [status(thm)], ['190', '203', '204'])).
% 1.52/1.76  thf('206', plain,
% 1.52/1.76      (![X22 : $i, X23 : $i]:
% 1.52/1.76         (~ (v1_partfun1 @ X23 @ X22)
% 1.52/1.76          | ((k1_relat_1 @ X23) = (X22))
% 1.52/1.76          | ~ (v4_relat_1 @ X23 @ X22)
% 1.52/1.76          | ~ (v1_relat_1 @ X23))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.52/1.76  thf('207', plain,
% 1.52/1.76      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.52/1.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.52/1.76        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.52/1.76        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['205', '206'])).
% 1.52/1.76  thf('208', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['89', '90'])).
% 1.52/1.76  thf('209', plain,
% 1.52/1.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.52/1.76         ((v1_relat_1 @ X2)
% 1.52/1.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.52/1.76  thf('210', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('sup-', [status(thm)], ['208', '209'])).
% 1.52/1.76  thf('211', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['89', '90'])).
% 1.52/1.76  thf('212', plain,
% 1.52/1.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.76         ((v4_relat_1 @ X5 @ X6)
% 1.52/1.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.52/1.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.52/1.76  thf('213', plain,
% 1.52/1.76      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup-', [status(thm)], ['211', '212'])).
% 1.52/1.76  thf('214', plain,
% 1.52/1.76      (![X1 : $i]:
% 1.52/1.76         (~ (v2_funct_1 @ X1)
% 1.52/1.76          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.52/1.76          | ~ (v1_funct_1 @ X1)
% 1.52/1.76          | ~ (v1_relat_1 @ X1))),
% 1.52/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.52/1.76  thf('215', plain,
% 1.52/1.76      (![X24 : $i]:
% 1.52/1.76         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.52/1.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.52/1.76  thf('216', plain,
% 1.52/1.76      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup-', [status(thm)], ['211', '212'])).
% 1.52/1.76  thf('217', plain,
% 1.52/1.76      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 1.52/1.76        | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['215', '216'])).
% 1.52/1.76  thf('218', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.52/1.76      inference('sup+', [status(thm)], ['13', '14'])).
% 1.52/1.76  thf('219', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('220', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['217', '218', '219'])).
% 1.52/1.76  thf('221', plain,
% 1.52/1.76      (![X1 : $i]:
% 1.52/1.76         (~ (v2_funct_1 @ X1)
% 1.52/1.76          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.52/1.76          | ~ (v1_funct_1 @ X1)
% 1.52/1.76          | ~ (v1_relat_1 @ X1))),
% 1.52/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.52/1.76  thf('222', plain,
% 1.52/1.76      (![X22 : $i, X23 : $i]:
% 1.52/1.76         (((k1_relat_1 @ X23) != (X22))
% 1.52/1.76          | (v1_partfun1 @ X23 @ X22)
% 1.52/1.76          | ~ (v4_relat_1 @ X23 @ X22)
% 1.52/1.76          | ~ (v1_relat_1 @ X23))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.52/1.76  thf('223', plain,
% 1.52/1.76      (![X23 : $i]:
% 1.52/1.76         (~ (v1_relat_1 @ X23)
% 1.52/1.76          | ~ (v4_relat_1 @ X23 @ (k1_relat_1 @ X23))
% 1.52/1.76          | (v1_partfun1 @ X23 @ (k1_relat_1 @ X23)))),
% 1.52/1.76      inference('simplify', [status(thm)], ['222'])).
% 1.52/1.76  thf('224', plain,
% 1.52/1.76      (![X0 : $i]:
% 1.52/1.76         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.52/1.76          | ~ (v1_relat_1 @ X0)
% 1.52/1.76          | ~ (v1_funct_1 @ X0)
% 1.52/1.76          | ~ (v2_funct_1 @ X0)
% 1.52/1.76          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.52/1.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['221', '223'])).
% 1.52/1.76  thf('225', plain,
% 1.52/1.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.52/1.76        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.52/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_relat_1 @ sk_C))),
% 1.52/1.76      inference('sup-', [status(thm)], ['220', '224'])).
% 1.52/1.76  thf('226', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('sup-', [status(thm)], ['208', '209'])).
% 1.52/1.76  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.76      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.76  thf('230', plain,
% 1.52/1.76      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.52/1.76      inference('demod', [status(thm)], ['225', '226', '227', '228', '229'])).
% 1.52/1.76  thf('231', plain,
% 1.52/1.76      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v2_funct_1 @ sk_C))),
% 1.52/1.76      inference('sup+', [status(thm)], ['214', '230'])).
% 1.52/1.76  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.76      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.76  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('235', plain,
% 1.52/1.76      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 1.52/1.76  thf('236', plain,
% 1.52/1.76      (![X22 : $i, X23 : $i]:
% 1.52/1.76         (~ (v1_partfun1 @ X23 @ X22)
% 1.52/1.76          | ((k1_relat_1 @ X23) = (X22))
% 1.52/1.76          | ~ (v4_relat_1 @ X23 @ X22)
% 1.52/1.76          | ~ (v1_relat_1 @ X23))),
% 1.52/1.76      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.52/1.76  thf('237', plain,
% 1.52/1.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.52/1.76        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.52/1.76        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['235', '236'])).
% 1.52/1.76  thf('238', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('sup-', [status(thm)], ['208', '209'])).
% 1.52/1.76  thf('239', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['217', '218', '219'])).
% 1.52/1.76  thf('240', plain,
% 1.52/1.76      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['237', '238', '239'])).
% 1.52/1.76  thf('241', plain,
% 1.52/1.76      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.52/1.76        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('demod', [status(thm)], ['207', '210', '213', '240'])).
% 1.52/1.76  thf('242', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['185'])).
% 1.52/1.76  thf('243', plain,
% 1.52/1.76      (((v1_xboole_0 @ k1_xboole_0)
% 1.52/1.76        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('demod', [status(thm)], ['241', '242'])).
% 1.52/1.76  thf('244', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.52/1.76      inference('sup-', [status(thm)], ['208', '209'])).
% 1.52/1.76  thf('245', plain,
% 1.52/1.76      (![X1 : $i]:
% 1.52/1.76         (~ (v2_funct_1 @ X1)
% 1.52/1.76          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.52/1.76          | ~ (v1_funct_1 @ X1)
% 1.52/1.76          | ~ (v1_relat_1 @ X1))),
% 1.52/1.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.52/1.76  thf(t65_relat_1, axiom,
% 1.52/1.76    (![A:$i]:
% 1.52/1.76     ( ( v1_relat_1 @ A ) =>
% 1.52/1.76       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.52/1.76         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.52/1.76  thf('246', plain,
% 1.52/1.76      (![X0 : $i]:
% 1.52/1.76         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.52/1.76          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 1.52/1.76          | ~ (v1_relat_1 @ X0))),
% 1.52/1.76      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.52/1.76  thf('247', plain,
% 1.52/1.76      (![X0 : $i]:
% 1.52/1.76         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 1.52/1.76          | ~ (v1_relat_1 @ X0)
% 1.52/1.76          | ~ (v1_funct_1 @ X0)
% 1.52/1.76          | ~ (v2_funct_1 @ X0)
% 1.52/1.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.52/1.76          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['245', '246'])).
% 1.52/1.76  thf('248', plain,
% 1.52/1.76      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 1.52/1.76        | ~ (v2_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.76        | ~ (v1_relat_1 @ sk_C)
% 1.52/1.76        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.52/1.76      inference('sup-', [status(thm)], ['244', '247'])).
% 1.52/1.76  thf('249', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.76  thf('251', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.76      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.76  thf('252', plain,
% 1.52/1.76      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 1.52/1.76        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.52/1.76      inference('demod', [status(thm)], ['248', '249', '250', '251'])).
% 1.52/1.76  thf('253', plain,
% 1.52/1.76      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['237', '238', '239'])).
% 1.52/1.76  thf('254', plain,
% 1.52/1.76      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.52/1.76        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.52/1.76      inference('demod', [status(thm)], ['252', '253'])).
% 1.52/1.76  thf('255', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['185'])).
% 1.52/1.76  thf('256', plain,
% 1.52/1.76      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.52/1.76        | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.52/1.76      inference('demod', [status(thm)], ['254', '255'])).
% 1.52/1.76  thf('257', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['256'])).
% 1.52/1.76  thf('258', plain,
% 1.52/1.76      (((v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (u1_struct_0 @ sk_B)))),
% 1.52/1.76      inference('demod', [status(thm)], ['243', '257'])).
% 1.52/1.76  thf('259', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('clc', [status(thm)], ['35', '36'])).
% 1.52/1.76  thf('260', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['256'])).
% 1.52/1.76  thf('261', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.76      inference('demod', [status(thm)], ['259', '260'])).
% 1.52/1.76  thf('262', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('clc', [status(thm)], ['258', '261'])).
% 1.52/1.76  thf('263', plain,
% 1.52/1.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 1.52/1.76      inference('demod', [status(thm)], ['187', '262'])).
% 1.52/1.76  thf('264', plain,
% 1.52/1.76      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.52/1.76         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.52/1.76          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.52/1.76          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.52/1.76  thf('265', plain,
% 1.52/1.76      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 1.52/1.76        | ((k1_xboole_0)
% 1.52/1.76            = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))))),
% 1.52/1.76      inference('sup-', [status(thm)], ['263', '264'])).
% 1.52/1.76  thf('266', plain,
% 1.52/1.76      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.52/1.76         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('simpl_trail', [status(thm)], ['112', '179'])).
% 1.52/1.76  thf('267', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['185'])).
% 1.52/1.76  thf('268', plain,
% 1.52/1.76      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 1.52/1.76         != (k2_relat_1 @ sk_C))),
% 1.52/1.76      inference('demod', [status(thm)], ['266', '267'])).
% 1.52/1.76  thf('269', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('clc', [status(thm)], ['258', '261'])).
% 1.52/1.76  thf('270', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['256'])).
% 1.52/1.76  thf('271', plain,
% 1.52/1.76      (((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 1.52/1.76         != (k1_xboole_0))),
% 1.52/1.76      inference('demod', [status(thm)], ['268', '269', '270'])).
% 1.52/1.76  thf('272', plain,
% 1.52/1.76      (~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 1.52/1.76      inference('simplify_reflect-', [status(thm)], ['265', '271'])).
% 1.52/1.76  thf('273', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ 
% 1.52/1.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.52/1.76      inference('demod', [status(thm)], ['89', '90'])).
% 1.52/1.76  thf('274', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.52/1.76      inference('simplify', [status(thm)], ['185'])).
% 1.52/1.76  thf('275', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ k1_xboole_0)))),
% 1.52/1.76      inference('demod', [status(thm)], ['273', '274'])).
% 1.52/1.76  thf('276', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B))),
% 1.52/1.76      inference('clc', [status(thm)], ['258', '261'])).
% 1.52/1.76  thf('277', plain,
% 1.52/1.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.52/1.76      inference('demod', [status(thm)], ['275', '276'])).
% 1.52/1.76  thf('278', plain,
% 1.52/1.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.76         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.52/1.76          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.52/1.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.52/1.76  thf('279', plain,
% 1.52/1.76      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 1.52/1.76        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.52/1.76      inference('sup-', [status(thm)], ['277', '278'])).
% 1.52/1.76  thf('280', plain,
% 1.52/1.76      (![X14 : $i, X15 : $i]:
% 1.52/1.76         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.52/1.76  thf('281', plain,
% 1.52/1.76      (![X14 : $i, X15 : $i]:
% 1.52/1.76         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 1.52/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.52/1.76  thf('282', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 1.52/1.76      inference('simplify', [status(thm)], ['281'])).
% 1.52/1.76  thf('283', plain,
% 1.52/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.76         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 1.52/1.76      inference('sup+', [status(thm)], ['280', '282'])).
% 1.52/1.76  thf('284', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 1.52/1.76      inference('eq_fact', [status(thm)], ['283'])).
% 1.52/1.76  thf('285', plain,
% 1.52/1.76      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 1.52/1.76      inference('demod', [status(thm)], ['279', '284'])).
% 1.52/1.76  thf('286', plain, ($false), inference('demod', [status(thm)], ['272', '285'])).
% 1.52/1.76  
% 1.52/1.76  % SZS output end Refutation
% 1.52/1.76  
% 1.52/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
