%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xe0LBeNxjA

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:48 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  345 (63309 expanded)
%              Number of leaves         :   45 (17994 expanded)
%              Depth                    :   35
%              Number of atoms          : 3039 (1611352 expanded)
%              Number of equality atoms :  214 (82210 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

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

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','38'])).

thf('40',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','51'])).

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

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('67',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','62','67','68'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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

thf('76',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','51'])).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

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

thf('91',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','92'])).

thf('94',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('101',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','38'])).

thf('105',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('110',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','110'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('114',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

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

thf('123',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('128',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('149',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125','134','135','149'])).

thf('151',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('153',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','111','112','113','151','152'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('156',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('168',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('169',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('170',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['99'])).

thf('171',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','176'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('179',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','110'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','110'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('183',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','183'])).

thf('185',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','184'])).

thf('186',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['99'])).

thf('193',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('194',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['153','193'])).

thf('195',plain,
    ( ( ( u1_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','194'])).

thf('196',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','195'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('198',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','200'])).

thf('202',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('203',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('204',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('206',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','51'])).

thf('207',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('208',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('211',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212'])).

thf('214',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','213'])).

thf('215',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('216',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('220',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['204','218','219'])).

thf('221',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('222',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('224',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('225',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('227',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('228',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('230',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('231',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('232',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('234',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != X22 )
      | ( v1_partfun1 @ X23 @ X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('235',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v4_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
      | ( v1_partfun1 @ X23 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['233','235'])).

thf('237',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['232','236'])).

thf('238',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('242',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['237','238','239','240','241'])).

thf('243',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['229','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['243','244','245','246'])).

thf('248',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('249',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('251',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('252',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['222','225','228','252'])).

thf('254',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['199'])).

thf('255',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('257',plain,(
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

thf('258',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['256','259'])).

thf('261',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('264',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('266',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['199'])).

thf('268',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['255','269'])).

thf('271',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('272',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['268'])).

thf('273',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['270','273'])).

thf('275',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['201','274'])).

thf('276',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('277',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['153','193'])).

thf('279',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['199'])).

thf('280',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['270','273'])).

thf('282',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['268'])).

thf('283',plain,(
    ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,(
    ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['277','283'])).

thf('285',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('286',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['199'])).

thf('287',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,
    ( k1_xboole_0
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['270','273'])).

thf('289',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('291',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('293',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('294',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['292','294'])).

thf('296',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['295'])).

thf('297',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['291','296'])).

thf('298',plain,(
    $false ),
    inference(demod,[status(thm)],['284','297'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xe0LBeNxjA
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.66/1.86  % Solved by: fo/fo7.sh
% 1.66/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.86  % done 836 iterations in 1.395s
% 1.66/1.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.66/1.86  % SZS output start Refutation
% 1.66/1.86  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.66/1.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.66/1.86  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.66/1.86  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.66/1.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.66/1.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.66/1.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.66/1.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.66/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.86  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.66/1.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.86  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.66/1.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.66/1.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.66/1.86  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.66/1.86  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.86  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.66/1.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.66/1.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.66/1.86  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.66/1.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.66/1.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.86  thf(d3_struct_0, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.66/1.86  thf('0', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('1', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf(t62_tops_2, conjecture,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( l1_struct_0 @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.66/1.86           ( ![C:$i]:
% 1.66/1.86             ( ( ( v1_funct_1 @ C ) & 
% 1.66/1.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.66/1.86                 ( m1_subset_1 @
% 1.66/1.86                   C @ 
% 1.66/1.86                   ( k1_zfmisc_1 @
% 1.66/1.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.66/1.86               ( ( ( ( k2_relset_1 @
% 1.66/1.86                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.66/1.86                     ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                   ( v2_funct_1 @ C ) ) =>
% 1.66/1.86                 ( ( ( k1_relset_1 @
% 1.66/1.86                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                       ( k2_tops_2 @
% 1.66/1.86                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                     ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                   ( ( k2_relset_1 @
% 1.66/1.86                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                       ( k2_tops_2 @
% 1.66/1.86                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.66/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.86    (~( ![A:$i]:
% 1.66/1.86        ( ( l1_struct_0 @ A ) =>
% 1.66/1.86          ( ![B:$i]:
% 1.66/1.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.66/1.86              ( ![C:$i]:
% 1.66/1.86                ( ( ( v1_funct_1 @ C ) & 
% 1.66/1.86                    ( v1_funct_2 @
% 1.66/1.86                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.66/1.86                    ( m1_subset_1 @
% 1.66/1.86                      C @ 
% 1.66/1.86                      ( k1_zfmisc_1 @
% 1.66/1.86                        ( k2_zfmisc_1 @
% 1.66/1.86                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.66/1.86                  ( ( ( ( k2_relset_1 @
% 1.66/1.86                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.66/1.86                        ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                      ( v2_funct_1 @ C ) ) =>
% 1.66/1.86                    ( ( ( k1_relset_1 @
% 1.66/1.86                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                          ( k2_tops_2 @
% 1.66/1.86                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                        ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                      ( ( k2_relset_1 @
% 1.66/1.86                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                          ( k2_tops_2 @
% 1.66/1.86                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.66/1.86    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.66/1.86  thf('2', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('3', plain,
% 1.66/1.86      (((m1_subset_1 @ sk_C @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['1', '2'])).
% 1.66/1.86  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('5', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['3', '4'])).
% 1.66/1.86  thf('6', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('7', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('8', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('9', plain,
% 1.66/1.86      (((m1_subset_1 @ sk_C @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['7', '8'])).
% 1.66/1.86  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('11', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['9', '10'])).
% 1.66/1.86  thf('12', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(redefinition_k2_relset_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.66/1.86  thf('13', plain,
% 1.66/1.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.66/1.86         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.66/1.86          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.66/1.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.86  thf('14', plain,
% 1.66/1.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['12', '13'])).
% 1.66/1.86  thf('15', plain,
% 1.66/1.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('17', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.86      inference('demod', [status(thm)], ['11', '16'])).
% 1.66/1.86  thf(cc5_funct_2, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.66/1.86       ( ![C:$i]:
% 1.66/1.86         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.66/1.86             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('18', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.66/1.86          | (v1_partfun1 @ X11 @ X12)
% 1.66/1.86          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 1.66/1.86          | ~ (v1_funct_1 @ X11)
% 1.66/1.86          | (v1_xboole_0 @ X13))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.66/1.86  thf('19', plain,
% 1.66/1.86      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['17', '18'])).
% 1.66/1.86  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('21', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('22', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('23', plain,
% 1.66/1.86      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['21', '22'])).
% 1.66/1.86  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('25', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['23', '24'])).
% 1.66/1.86  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('27', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['25', '26'])).
% 1.66/1.86  thf('28', plain,
% 1.66/1.86      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('demod', [status(thm)], ['19', '20', '27'])).
% 1.66/1.86  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('30', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf(fc2_struct_0, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.66/1.86       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.66/1.86  thf('31', plain,
% 1.66/1.86      (![X28 : $i]:
% 1.66/1.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.66/1.86          | ~ (l1_struct_0 @ X28)
% 1.66/1.86          | (v2_struct_0 @ X28))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.66/1.86  thf('32', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.66/1.86          | ~ (l1_struct_0 @ X0)
% 1.66/1.86          | (v2_struct_0 @ X0)
% 1.66/1.86          | ~ (l1_struct_0 @ X0))),
% 1.66/1.86      inference('sup-', [status(thm)], ['30', '31'])).
% 1.66/1.86  thf('33', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((v2_struct_0 @ X0)
% 1.66/1.86          | ~ (l1_struct_0 @ X0)
% 1.66/1.86          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.66/1.86      inference('simplify', [status(thm)], ['32'])).
% 1.66/1.86  thf('34', plain,
% 1.66/1.86      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B)
% 1.66/1.86        | (v2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup-', [status(thm)], ['29', '33'])).
% 1.66/1.86  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('36', plain,
% 1.66/1.86      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['34', '35'])).
% 1.66/1.86  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('38', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('clc', [status(thm)], ['36', '37'])).
% 1.66/1.86  thf('39', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('clc', [status(thm)], ['28', '38'])).
% 1.66/1.86  thf('40', plain,
% 1.66/1.86      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['6', '39'])).
% 1.66/1.86  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('42', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['40', '41'])).
% 1.66/1.86  thf(d4_partfun1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.66/1.86       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.66/1.86  thf('43', plain,
% 1.66/1.86      (![X22 : $i, X23 : $i]:
% 1.66/1.86         (~ (v1_partfun1 @ X23 @ X22)
% 1.66/1.86          | ((k1_relat_1 @ X23) = (X22))
% 1.66/1.86          | ~ (v4_relat_1 @ X23 @ X22)
% 1.66/1.86          | ~ (v1_relat_1 @ X23))),
% 1.66/1.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.86  thf('44', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ sk_C)
% 1.66/1.86        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.66/1.86        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['42', '43'])).
% 1.66/1.86  thf('45', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(cc1_relset_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( v1_relat_1 @ C ) ))).
% 1.66/1.86  thf('46', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         ((v1_relat_1 @ X2)
% 1.66/1.86          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.66/1.86  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.86      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.86  thf('48', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['3', '4'])).
% 1.66/1.86  thf(cc2_relset_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.66/1.86  thf('49', plain,
% 1.66/1.86      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.86         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.86          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.86  thf('50', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['48', '49'])).
% 1.66/1.86  thf('51', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.86  thf('52', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['5', '51'])).
% 1.66/1.86  thf(t31_funct_2, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.86       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.66/1.86         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.66/1.86           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.66/1.86           ( m1_subset_1 @
% 1.66/1.86             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('53', plain,
% 1.66/1.86      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ X24)
% 1.66/1.86          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.66/1.86          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 1.66/1.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.66/1.86          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.66/1.86          | ~ (v1_funct_1 @ X24))),
% 1.66/1.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.66/1.86  thf('54', plain,
% 1.66/1.86      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.66/1.86        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.86           (k1_relat_1 @ sk_C))
% 1.66/1.86        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86            != (u1_struct_0 @ sk_B))
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.86  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('56', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('57', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('58', plain,
% 1.66/1.86      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['56', '57'])).
% 1.66/1.86  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('60', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['58', '59'])).
% 1.66/1.86  thf('61', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.86  thf('62', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['60', '61'])).
% 1.66/1.86  thf('63', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['3', '4'])).
% 1.66/1.86  thf('64', plain,
% 1.66/1.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.66/1.86         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.66/1.86          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.66/1.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.86  thf('65', plain,
% 1.66/1.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['63', '64'])).
% 1.66/1.86  thf('66', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.86  thf('67', plain,
% 1.66/1.86      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['65', '66'])).
% 1.66/1.86  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('69', plain,
% 1.66/1.86      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.86         (k1_relat_1 @ sk_C))
% 1.66/1.86        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.66/1.86      inference('demod', [status(thm)], ['54', '55', '62', '67', '68'])).
% 1.66/1.86  thf('70', plain,
% 1.66/1.86      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B)
% 1.66/1.86        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.86           (k1_relat_1 @ sk_C)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['0', '69'])).
% 1.66/1.86  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('73', plain,
% 1.66/1.86      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.66/1.86        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.86           (k1_relat_1 @ sk_C)))),
% 1.66/1.86      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.66/1.86  thf('74', plain,
% 1.66/1.86      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.86        (k1_relat_1 @ sk_C))),
% 1.66/1.86      inference('simplify', [status(thm)], ['73'])).
% 1.66/1.86  thf('75', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf(d1_funct_2, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.66/1.86           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.66/1.86             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.66/1.86         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.86           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.66/1.86             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.66/1.86  thf(zf_stmt_1, axiom,
% 1.66/1.86    (![B:$i,A:$i]:
% 1.66/1.86     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.66/1.86       ( zip_tseitin_0 @ B @ A ) ))).
% 1.66/1.86  thf('76', plain,
% 1.66/1.86      (![X14 : $i, X15 : $i]:
% 1.66/1.86         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.86  thf('77', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('78', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['5', '51'])).
% 1.66/1.86  thf('79', plain,
% 1.66/1.86      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ X24)
% 1.66/1.86          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.66/1.86          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 1.66/1.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.66/1.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.66/1.86          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.66/1.86          | ~ (v1_funct_1 @ X24))),
% 1.66/1.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.66/1.86  thf('80', plain,
% 1.66/1.86      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.66/1.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86           (k1_zfmisc_1 @ 
% 1.66/1.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.66/1.86        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86            != (u1_struct_0 @ sk_B))
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['78', '79'])).
% 1.66/1.86  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('82', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['60', '61'])).
% 1.66/1.86  thf('83', plain,
% 1.66/1.86      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['65', '66'])).
% 1.66/1.86  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('85', plain,
% 1.66/1.86      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.66/1.86        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.66/1.86      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 1.66/1.86  thf('86', plain,
% 1.66/1.86      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B)
% 1.66/1.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86           (k1_zfmisc_1 @ 
% 1.66/1.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['77', '85'])).
% 1.66/1.86  thf('87', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('89', plain,
% 1.66/1.86      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.66/1.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86           (k1_zfmisc_1 @ 
% 1.66/1.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.66/1.86      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.66/1.86  thf('90', plain,
% 1.66/1.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['89'])).
% 1.66/1.86  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.66/1.86  thf(zf_stmt_3, axiom,
% 1.66/1.86    (![C:$i,B:$i,A:$i]:
% 1.66/1.86     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.66/1.86       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.66/1.86  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.66/1.86  thf(zf_stmt_5, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.66/1.86         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.66/1.86           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.66/1.86             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.66/1.86  thf('91', plain,
% 1.66/1.86      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.66/1.86         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.66/1.86          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.66/1.86          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.66/1.86  thf('92', plain,
% 1.66/1.86      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86         (u1_struct_0 @ sk_B))
% 1.66/1.86        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['90', '91'])).
% 1.66/1.86  thf('93', plain,
% 1.66/1.86      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.66/1.86        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86           (u1_struct_0 @ sk_B)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['76', '92'])).
% 1.66/1.86  thf('94', plain,
% 1.66/1.86      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.86        (k1_relat_1 @ sk_C))),
% 1.66/1.86      inference('simplify', [status(thm)], ['73'])).
% 1.66/1.86  thf('95', plain,
% 1.66/1.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.66/1.86         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.66/1.86          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.66/1.86          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.86  thf('96', plain,
% 1.66/1.86      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86           (u1_struct_0 @ sk_B))
% 1.66/1.86        | ((u1_struct_0 @ sk_B)
% 1.66/1.86            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86               (k2_funct_1 @ sk_C))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['94', '95'])).
% 1.66/1.86  thf('97', plain,
% 1.66/1.86      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.66/1.86        | ((u1_struct_0 @ sk_B)
% 1.66/1.86            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86               (k2_funct_1 @ sk_C))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['93', '96'])).
% 1.66/1.86  thf('98', plain,
% 1.66/1.86      (![X27 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('99', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_B))
% 1.66/1.86        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86            != (k2_struct_0 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('100', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('split', [status(esa)], ['99'])).
% 1.66/1.86  thf('101', plain,
% 1.66/1.86      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86           != (k2_struct_0 @ sk_B))
% 1.66/1.86         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['98', '100'])).
% 1.66/1.86  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('103', plain,
% 1.66/1.87      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          != (k2_struct_0 @ sk_B)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_B))))),
% 1.66/1.87      inference('demod', [status(thm)], ['101', '102'])).
% 1.66/1.87  thf('104', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.66/1.87      inference('clc', [status(thm)], ['28', '38'])).
% 1.66/1.87  thf('105', plain,
% 1.66/1.87      (![X22 : $i, X23 : $i]:
% 1.66/1.87         (~ (v1_partfun1 @ X23 @ X22)
% 1.66/1.87          | ((k1_relat_1 @ X23) = (X22))
% 1.66/1.87          | ~ (v4_relat_1 @ X23 @ X22)
% 1.66/1.87          | ~ (v1_relat_1 @ X23))),
% 1.66/1.87      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.87  thf('106', plain,
% 1.66/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.66/1.87        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.66/1.87        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['104', '105'])).
% 1.66/1.87  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.87  thf('108', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('109', plain,
% 1.66/1.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.87         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.87          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.87  thf('110', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.66/1.87      inference('sup-', [status(thm)], ['108', '109'])).
% 1.66/1.87  thf('111', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['106', '107', '110'])).
% 1.66/1.87  thf('112', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['106', '107', '110'])).
% 1.66/1.87  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('114', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('115', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.87      inference('demod', [status(thm)], ['3', '4'])).
% 1.66/1.87  thf('116', plain,
% 1.66/1.87      (((m1_subset_1 @ sk_C @ 
% 1.66/1.87         (k1_zfmisc_1 @ 
% 1.66/1.87          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.66/1.87        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['114', '115'])).
% 1.66/1.87  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('118', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.66/1.87      inference('demod', [status(thm)], ['116', '117'])).
% 1.66/1.87  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('120', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.87      inference('demod', [status(thm)], ['118', '119'])).
% 1.66/1.87  thf('121', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.87  thf('122', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.87      inference('demod', [status(thm)], ['120', '121'])).
% 1.66/1.87  thf(d4_tops_2, axiom,
% 1.66/1.87    (![A:$i,B:$i,C:$i]:
% 1.66/1.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.87       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.66/1.87         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.66/1.87  thf('123', plain,
% 1.66/1.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.66/1.87         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 1.66/1.87          | ~ (v2_funct_1 @ X31)
% 1.66/1.87          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 1.66/1.87          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.66/1.87          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 1.66/1.87          | ~ (v1_funct_1 @ X31))),
% 1.66/1.87      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.66/1.87  thf('124', plain,
% 1.66/1.87      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.87        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87            = (k2_funct_1 @ sk_C))
% 1.66/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.66/1.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87            != (k2_relat_1 @ sk_C)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['122', '123'])).
% 1.66/1.87  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('126', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('127', plain,
% 1.66/1.87      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.87      inference('demod', [status(thm)], ['58', '59'])).
% 1.66/1.87  thf('128', plain,
% 1.66/1.87      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.66/1.87        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['126', '127'])).
% 1.66/1.87  thf('129', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('130', plain,
% 1.66/1.87      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.66/1.87  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('132', plain,
% 1.66/1.87      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['130', '131'])).
% 1.66/1.87  thf('133', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.87  thf('134', plain,
% 1.66/1.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['132', '133'])).
% 1.66/1.87  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('136', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('137', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('138', plain,
% 1.66/1.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87         = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('139', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87          = (k2_struct_0 @ sk_B))
% 1.66/1.87        | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.87      inference('sup+', [status(thm)], ['137', '138'])).
% 1.66/1.87  thf('140', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('141', plain,
% 1.66/1.87      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87         = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('demod', [status(thm)], ['139', '140'])).
% 1.66/1.87  thf('142', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87          = (k2_struct_0 @ sk_B))
% 1.66/1.87        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['136', '141'])).
% 1.66/1.87  thf('143', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('144', plain,
% 1.66/1.87      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87         = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('demod', [status(thm)], ['142', '143'])).
% 1.66/1.87  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('146', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('147', plain,
% 1.66/1.87      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87         = (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['144', '145', '146'])).
% 1.66/1.87  thf('148', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.87  thf('149', plain,
% 1.66/1.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87         = (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['147', '148'])).
% 1.66/1.87  thf('150', plain,
% 1.66/1.87      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87          = (k2_funct_1 @ sk_C))
% 1.66/1.87        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.66/1.87      inference('demod', [status(thm)], ['124', '125', '134', '135', '149'])).
% 1.66/1.87  thf('151', plain,
% 1.66/1.87      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87         = (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('simplify', [status(thm)], ['150'])).
% 1.66/1.87  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('153', plain,
% 1.66/1.87      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.87          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_B))))),
% 1.66/1.87      inference('demod', [status(thm)],
% 1.66/1.87                ['103', '111', '112', '113', '151', '152'])).
% 1.66/1.87  thf(t55_funct_1, axiom,
% 1.66/1.87    (![A:$i]:
% 1.66/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.87       ( ( v2_funct_1 @ A ) =>
% 1.66/1.87         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.66/1.87           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.66/1.87  thf('154', plain,
% 1.66/1.87      (![X1 : $i]:
% 1.66/1.87         (~ (v2_funct_1 @ X1)
% 1.66/1.87          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.66/1.87          | ~ (v1_funct_1 @ X1)
% 1.66/1.87          | ~ (v1_relat_1 @ X1))),
% 1.66/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.87  thf('155', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.87      inference('demod', [status(thm)], ['120', '121'])).
% 1.66/1.87  thf('156', plain,
% 1.66/1.87      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.87         (~ (v2_funct_1 @ X24)
% 1.66/1.87          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.66/1.87          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 1.66/1.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.66/1.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.66/1.87          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.66/1.87          | ~ (v1_funct_1 @ X24))),
% 1.66/1.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.66/1.87  thf('157', plain,
% 1.66/1.87      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.87        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87           (k1_zfmisc_1 @ 
% 1.66/1.87            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.66/1.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87            != (k2_relat_1 @ sk_C))
% 1.66/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['155', '156'])).
% 1.66/1.87  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('159', plain,
% 1.66/1.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['132', '133'])).
% 1.66/1.87  thf('160', plain,
% 1.66/1.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87         = (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['147', '148'])).
% 1.66/1.87  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('162', plain,
% 1.66/1.87      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87         (k1_zfmisc_1 @ 
% 1.66/1.87          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.66/1.87        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.66/1.87      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 1.66/1.87  thf('163', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.87      inference('simplify', [status(thm)], ['162'])).
% 1.66/1.87  thf('164', plain,
% 1.66/1.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.66/1.87         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.66/1.87          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.66/1.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.87  thf('165', plain,
% 1.66/1.87      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.87         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['163', '164'])).
% 1.66/1.87  thf('166', plain,
% 1.66/1.87      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.87         = (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('simplify', [status(thm)], ['150'])).
% 1.66/1.87  thf('167', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('168', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('169', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('170', plain,
% 1.66/1.87      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          != (k2_struct_0 @ sk_A)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('split', [status(esa)], ['99'])).
% 1.66/1.87  thf('171', plain,
% 1.66/1.87      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87           != (k2_struct_0 @ sk_A))
% 1.66/1.87         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['169', '170'])).
% 1.66/1.87  thf('172', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('173', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          != (k2_struct_0 @ sk_A)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('demod', [status(thm)], ['171', '172'])).
% 1.66/1.87  thf('174', plain,
% 1.66/1.87      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87           != (k2_struct_0 @ sk_A))
% 1.66/1.87         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['168', '173'])).
% 1.66/1.87  thf('175', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('176', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          != (k2_struct_0 @ sk_A)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('demod', [status(thm)], ['174', '175'])).
% 1.66/1.87  thf('177', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.66/1.87          != (k2_struct_0 @ sk_A)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['167', '176'])).
% 1.66/1.87  thf('178', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('179', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.66/1.87          != (k2_struct_0 @ sk_A)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('demod', [status(thm)], ['177', '178'])).
% 1.66/1.87  thf('180', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['106', '107', '110'])).
% 1.66/1.87  thf('181', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['106', '107', '110'])).
% 1.66/1.87  thf('182', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.87      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.66/1.87  thf('183', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.87          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.66/1.87          != (k1_relat_1 @ sk_C)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 1.66/1.87  thf('184', plain,
% 1.66/1.87      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.87          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['166', '183'])).
% 1.66/1.87  thf('185', plain,
% 1.66/1.87      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['165', '184'])).
% 1.66/1.87  thf('186', plain,
% 1.66/1.87      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.66/1.87         | ~ (v1_relat_1 @ sk_C)
% 1.66/1.87         | ~ (v1_funct_1 @ sk_C)
% 1.66/1.87         | ~ (v2_funct_1 @ sk_C)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['154', '185'])).
% 1.66/1.87  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.87  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('190', plain,
% 1.66/1.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.66/1.87         <= (~
% 1.66/1.87             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87                = (k2_struct_0 @ sk_A))))),
% 1.66/1.87      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 1.66/1.87  thf('191', plain,
% 1.66/1.87      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          = (k2_struct_0 @ sk_A)))),
% 1.66/1.87      inference('simplify', [status(thm)], ['190'])).
% 1.66/1.87  thf('192', plain,
% 1.66/1.87      (~
% 1.66/1.87       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          = (k2_struct_0 @ sk_B))) | 
% 1.66/1.87       ~
% 1.66/1.87       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          = (k2_struct_0 @ sk_A)))),
% 1.66/1.87      inference('split', [status(esa)], ['99'])).
% 1.66/1.87  thf('193', plain,
% 1.66/1.87      (~
% 1.66/1.87       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.87          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.87          = (k2_struct_0 @ sk_B)))),
% 1.66/1.87      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.66/1.87  thf('194', plain,
% 1.66/1.87      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.87         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('simpl_trail', [status(thm)], ['153', '193'])).
% 1.66/1.87  thf('195', plain,
% 1.66/1.87      ((((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 1.66/1.87        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['97', '194'])).
% 1.66/1.87  thf('196', plain,
% 1.66/1.87      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 1.66/1.87        | ~ (l1_struct_0 @ sk_B)
% 1.66/1.87        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['75', '195'])).
% 1.66/1.87  thf('197', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('198', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('199', plain,
% 1.66/1.87      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.66/1.87        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.66/1.87      inference('demod', [status(thm)], ['196', '197', '198'])).
% 1.66/1.87  thf('200', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['199'])).
% 1.66/1.87  thf('201', plain,
% 1.66/1.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ k1_xboole_0)),
% 1.66/1.87      inference('demod', [status(thm)], ['74', '200'])).
% 1.66/1.87  thf('202', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.87      inference('simplify', [status(thm)], ['89'])).
% 1.66/1.87  thf('203', plain,
% 1.66/1.87      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.87         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.66/1.87          | (v1_partfun1 @ X11 @ X12)
% 1.66/1.87          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 1.66/1.87          | ~ (v1_funct_1 @ X11)
% 1.66/1.87          | (v1_xboole_0 @ X13))),
% 1.66/1.87      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.66/1.87  thf('204', plain,
% 1.66/1.87      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.66/1.87        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.87        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.87             (k1_relat_1 @ sk_C))
% 1.66/1.87        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['202', '203'])).
% 1.66/1.87  thf('205', plain,
% 1.66/1.87      (![X27 : $i]:
% 1.66/1.87         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.66/1.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.87  thf('206', plain,
% 1.66/1.87      ((m1_subset_1 @ sk_C @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.87      inference('demod', [status(thm)], ['5', '51'])).
% 1.66/1.87  thf('207', plain,
% 1.66/1.87      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.87         (~ (v2_funct_1 @ X24)
% 1.66/1.87          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.66/1.87          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 1.66/1.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.66/1.87          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.66/1.87          | ~ (v1_funct_1 @ X24))),
% 1.66/1.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.66/1.87  thf('208', plain,
% 1.66/1.87      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.66/1.87        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87            != (u1_struct_0 @ sk_B))
% 1.66/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['206', '207'])).
% 1.66/1.87  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('210', plain,
% 1.66/1.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.66/1.87      inference('demod', [status(thm)], ['60', '61'])).
% 1.66/1.87  thf('211', plain,
% 1.66/1.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.87         = (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['65', '66'])).
% 1.66/1.87  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('213', plain,
% 1.66/1.87      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.87        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('demod', [status(thm)], ['208', '209', '210', '211', '212'])).
% 1.66/1.87  thf('214', plain,
% 1.66/1.87      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.66/1.87        | ~ (l1_struct_0 @ sk_B)
% 1.66/1.87        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['205', '213'])).
% 1.66/1.87  thf('215', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.66/1.87  thf('216', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('217', plain,
% 1.66/1.87      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.66/1.87        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.87      inference('demod', [status(thm)], ['214', '215', '216'])).
% 1.66/1.87  thf('218', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('simplify', [status(thm)], ['217'])).
% 1.66/1.87  thf('219', plain,
% 1.66/1.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.66/1.87        (k1_relat_1 @ sk_C))),
% 1.66/1.87      inference('simplify', [status(thm)], ['73'])).
% 1.66/1.87  thf('220', plain,
% 1.66/1.87      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.66/1.87        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('demod', [status(thm)], ['204', '218', '219'])).
% 1.66/1.87  thf('221', plain,
% 1.66/1.87      (![X22 : $i, X23 : $i]:
% 1.66/1.87         (~ (v1_partfun1 @ X23 @ X22)
% 1.66/1.87          | ((k1_relat_1 @ X23) = (X22))
% 1.66/1.87          | ~ (v4_relat_1 @ X23 @ X22)
% 1.66/1.87          | ~ (v1_relat_1 @ X23))),
% 1.66/1.87      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.87  thf('222', plain,
% 1.66/1.87      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.66/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.87        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.66/1.87        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['220', '221'])).
% 1.66/1.87  thf('223', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.87      inference('simplify', [status(thm)], ['162'])).
% 1.66/1.87  thf('224', plain,
% 1.66/1.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.87         ((v1_relat_1 @ X2)
% 1.66/1.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.66/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.66/1.87  thf('225', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['223', '224'])).
% 1.66/1.87  thf('226', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.87      inference('simplify', [status(thm)], ['89'])).
% 1.66/1.87  thf('227', plain,
% 1.66/1.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.87         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.87          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.87  thf('228', plain,
% 1.66/1.87      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.66/1.87      inference('sup-', [status(thm)], ['226', '227'])).
% 1.66/1.87  thf('229', plain,
% 1.66/1.87      (![X1 : $i]:
% 1.66/1.87         (~ (v2_funct_1 @ X1)
% 1.66/1.87          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.66/1.87          | ~ (v1_funct_1 @ X1)
% 1.66/1.87          | ~ (v1_relat_1 @ X1))),
% 1.66/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.87  thf('230', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.87      inference('simplify', [status(thm)], ['162'])).
% 1.66/1.87  thf('231', plain,
% 1.66/1.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.87         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.87          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.87  thf('232', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['230', '231'])).
% 1.66/1.87  thf('233', plain,
% 1.66/1.87      (![X1 : $i]:
% 1.66/1.87         (~ (v2_funct_1 @ X1)
% 1.66/1.87          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.66/1.87          | ~ (v1_funct_1 @ X1)
% 1.66/1.87          | ~ (v1_relat_1 @ X1))),
% 1.66/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.87  thf('234', plain,
% 1.66/1.87      (![X22 : $i, X23 : $i]:
% 1.66/1.87         (((k1_relat_1 @ X23) != (X22))
% 1.66/1.87          | (v1_partfun1 @ X23 @ X22)
% 1.66/1.87          | ~ (v4_relat_1 @ X23 @ X22)
% 1.66/1.87          | ~ (v1_relat_1 @ X23))),
% 1.66/1.87      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.87  thf('235', plain,
% 1.66/1.87      (![X23 : $i]:
% 1.66/1.87         (~ (v1_relat_1 @ X23)
% 1.66/1.87          | ~ (v4_relat_1 @ X23 @ (k1_relat_1 @ X23))
% 1.66/1.87          | (v1_partfun1 @ X23 @ (k1_relat_1 @ X23)))),
% 1.66/1.87      inference('simplify', [status(thm)], ['234'])).
% 1.66/1.87  thf('236', plain,
% 1.66/1.87      (![X0 : $i]:
% 1.66/1.87         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.66/1.87          | ~ (v1_relat_1 @ X0)
% 1.66/1.87          | ~ (v1_funct_1 @ X0)
% 1.66/1.87          | ~ (v2_funct_1 @ X0)
% 1.66/1.87          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.66/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['233', '235'])).
% 1.66/1.87  thf('237', plain,
% 1.66/1.87      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.87        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.66/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['232', '236'])).
% 1.66/1.87  thf('238', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['223', '224'])).
% 1.66/1.87  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('241', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.87  thf('242', plain,
% 1.66/1.87      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.87      inference('demod', [status(thm)], ['237', '238', '239', '240', '241'])).
% 1.66/1.87  thf('243', plain,
% 1.66/1.87      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.66/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup+', [status(thm)], ['229', '242'])).
% 1.66/1.87  thf('244', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.87  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('246', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('247', plain,
% 1.66/1.87      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['243', '244', '245', '246'])).
% 1.66/1.87  thf('248', plain,
% 1.66/1.87      (![X22 : $i, X23 : $i]:
% 1.66/1.87         (~ (v1_partfun1 @ X23 @ X22)
% 1.66/1.87          | ((k1_relat_1 @ X23) = (X22))
% 1.66/1.87          | ~ (v4_relat_1 @ X23 @ X22)
% 1.66/1.87          | ~ (v1_relat_1 @ X23))),
% 1.66/1.87      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.87  thf('249', plain,
% 1.66/1.87      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.87        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.87        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['247', '248'])).
% 1.66/1.87  thf('250', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['223', '224'])).
% 1.66/1.87  thf('251', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['230', '231'])).
% 1.66/1.87  thf('252', plain,
% 1.66/1.87      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['249', '250', '251'])).
% 1.66/1.87  thf('253', plain,
% 1.66/1.87      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.66/1.87        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('demod', [status(thm)], ['222', '225', '228', '252'])).
% 1.66/1.87  thf('254', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['199'])).
% 1.66/1.87  thf('255', plain,
% 1.66/1.87      (((v1_xboole_0 @ k1_xboole_0)
% 1.66/1.87        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('demod', [status(thm)], ['253', '254'])).
% 1.66/1.87  thf('256', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.87      inference('sup-', [status(thm)], ['223', '224'])).
% 1.66/1.87  thf('257', plain,
% 1.66/1.87      (![X1 : $i]:
% 1.66/1.87         (~ (v2_funct_1 @ X1)
% 1.66/1.87          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.66/1.87          | ~ (v1_funct_1 @ X1)
% 1.66/1.87          | ~ (v1_relat_1 @ X1))),
% 1.66/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.87  thf(t65_relat_1, axiom,
% 1.66/1.87    (![A:$i]:
% 1.66/1.87     ( ( v1_relat_1 @ A ) =>
% 1.66/1.87       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.66/1.87         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.66/1.87  thf('258', plain,
% 1.66/1.87      (![X0 : $i]:
% 1.66/1.87         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.66/1.87          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 1.66/1.87          | ~ (v1_relat_1 @ X0))),
% 1.66/1.87      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.66/1.87  thf('259', plain,
% 1.66/1.87      (![X0 : $i]:
% 1.66/1.87         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 1.66/1.87          | ~ (v1_relat_1 @ X0)
% 1.66/1.87          | ~ (v1_funct_1 @ X0)
% 1.66/1.87          | ~ (v2_funct_1 @ X0)
% 1.66/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.66/1.87          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['257', '258'])).
% 1.66/1.87  thf('260', plain,
% 1.66/1.87      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 1.66/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.66/1.87        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.66/1.87      inference('sup-', [status(thm)], ['256', '259'])).
% 1.66/1.87  thf('261', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.87  thf('263', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.87  thf('264', plain,
% 1.66/1.87      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 1.66/1.87        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.66/1.87      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 1.66/1.87  thf('265', plain,
% 1.66/1.87      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['249', '250', '251'])).
% 1.66/1.87  thf('266', plain,
% 1.66/1.87      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.66/1.87        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.66/1.87      inference('demod', [status(thm)], ['264', '265'])).
% 1.66/1.87  thf('267', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['199'])).
% 1.66/1.87  thf('268', plain,
% 1.66/1.87      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.66/1.87        | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.66/1.87      inference('demod', [status(thm)], ['266', '267'])).
% 1.66/1.87  thf('269', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['268'])).
% 1.66/1.87  thf('270', plain,
% 1.66/1.87      (((v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (u1_struct_0 @ sk_B)))),
% 1.66/1.87      inference('demod', [status(thm)], ['255', '269'])).
% 1.66/1.87  thf('271', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('clc', [status(thm)], ['36', '37'])).
% 1.66/1.87  thf('272', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['268'])).
% 1.66/1.87  thf('273', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.66/1.87      inference('demod', [status(thm)], ['271', '272'])).
% 1.66/1.87  thf('274', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B))),
% 1.66/1.87      inference('clc', [status(thm)], ['270', '273'])).
% 1.66/1.87  thf('275', plain,
% 1.66/1.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 1.66/1.87      inference('demod', [status(thm)], ['201', '274'])).
% 1.66/1.87  thf('276', plain,
% 1.66/1.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.66/1.87         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.66/1.87          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.66/1.87          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.87  thf('277', plain,
% 1.66/1.87      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 1.66/1.87        | ((k1_xboole_0)
% 1.66/1.87            = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))))),
% 1.66/1.87      inference('sup-', [status(thm)], ['275', '276'])).
% 1.66/1.87  thf('278', plain,
% 1.66/1.87      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.87         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('simpl_trail', [status(thm)], ['153', '193'])).
% 1.66/1.87  thf('279', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['199'])).
% 1.66/1.87  thf('280', plain,
% 1.66/1.87      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 1.66/1.87         != (k2_relat_1 @ sk_C))),
% 1.66/1.87      inference('demod', [status(thm)], ['278', '279'])).
% 1.66/1.87  thf('281', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B))),
% 1.66/1.87      inference('clc', [status(thm)], ['270', '273'])).
% 1.66/1.87  thf('282', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['268'])).
% 1.66/1.87  thf('283', plain,
% 1.66/1.87      (((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 1.66/1.87         != (k1_xboole_0))),
% 1.66/1.87      inference('demod', [status(thm)], ['280', '281', '282'])).
% 1.66/1.87  thf('284', plain,
% 1.66/1.87      (~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 1.66/1.87      inference('simplify_reflect-', [status(thm)], ['277', '283'])).
% 1.66/1.87  thf('285', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ 
% 1.66/1.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.87      inference('simplify', [status(thm)], ['89'])).
% 1.66/1.87  thf('286', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.66/1.87      inference('simplify', [status(thm)], ['199'])).
% 1.66/1.87  thf('287', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ k1_xboole_0)))),
% 1.66/1.87      inference('demod', [status(thm)], ['285', '286'])).
% 1.66/1.87  thf('288', plain, (((k1_xboole_0) = (u1_struct_0 @ sk_B))),
% 1.66/1.87      inference('clc', [status(thm)], ['270', '273'])).
% 1.66/1.87  thf('289', plain,
% 1.66/1.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.66/1.87      inference('demod', [status(thm)], ['287', '288'])).
% 1.66/1.87  thf('290', plain,
% 1.66/1.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.66/1.87         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.66/1.87          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.66/1.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.66/1.87  thf('291', plain,
% 1.66/1.87      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)
% 1.66/1.87        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.66/1.87      inference('sup-', [status(thm)], ['289', '290'])).
% 1.66/1.87  thf('292', plain,
% 1.66/1.87      (![X14 : $i, X15 : $i]:
% 1.66/1.87         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.87  thf('293', plain,
% 1.66/1.87      (![X14 : $i, X15 : $i]:
% 1.66/1.87         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 1.66/1.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.66/1.87  thf('294', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 1.66/1.87      inference('simplify', [status(thm)], ['293'])).
% 1.66/1.87  thf('295', plain,
% 1.66/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.87         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 1.66/1.87      inference('sup+', [status(thm)], ['292', '294'])).
% 1.66/1.87  thf('296', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 1.66/1.87      inference('eq_fact', [status(thm)], ['295'])).
% 1.66/1.87  thf('297', plain,
% 1.66/1.87      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ k1_xboole_0)),
% 1.66/1.87      inference('demod', [status(thm)], ['291', '296'])).
% 1.66/1.87  thf('298', plain, ($false), inference('demod', [status(thm)], ['284', '297'])).
% 1.66/1.87  
% 1.66/1.87  % SZS output end Refutation
% 1.66/1.87  
% 1.66/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
