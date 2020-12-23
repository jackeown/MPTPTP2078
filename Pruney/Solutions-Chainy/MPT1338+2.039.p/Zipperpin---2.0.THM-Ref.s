%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iRh9DIT1ZV

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:53 EST 2020

% Result     : Theorem 3.80s
% Output     : Refutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 737 expanded)
%              Number of leaves         :   50 ( 232 expanded)
%              Depth                    :   24
%              Number of atoms          : 2176 (19374 expanded)
%              Number of equality atoms :  172 (1085 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(rc20_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( u1_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('32',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('49',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('56',plain,(
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

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','65','66','74'])).

thf('76',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('78',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('82',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','94'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','76','95'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('99',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
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

thf('120',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['134','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('145',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','121','132','133','145'])).

thf('147',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('152',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['148','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['147','164'])).

thf('166',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['107','165'])).

thf('167',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('169',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['167','168'])).

thf('170',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['96','169'])).

thf('171',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','172'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('174',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('175',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('176',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('177',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['175','176'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('179',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ X27 )
      | ( ( k3_tarski @ X27 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( sk_B @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['177','181'])).

thf('183',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('184',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('185',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('186',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('187',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_struct_0 @ sk_B_2 ),
    inference(demod,[status(thm)],['184','187','188'])).

thf('190',plain,(
    $false ),
    inference(demod,[status(thm)],['0','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iRh9DIT1ZV
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.80/4.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.80/4.03  % Solved by: fo/fo7.sh
% 3.80/4.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.80/4.03  % done 2478 iterations in 3.581s
% 3.80/4.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.80/4.03  % SZS output start Refutation
% 3.80/4.03  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.80/4.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.80/4.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.80/4.03  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.80/4.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.80/4.03  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 3.80/4.03  thf(sk_A_type, type, sk_A: $i).
% 3.80/4.03  thf(sk_B_type, type, sk_B: $i > $i).
% 3.80/4.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.80/4.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.80/4.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.80/4.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.80/4.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.80/4.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.80/4.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.80/4.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.80/4.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.80/4.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.80/4.03  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.80/4.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.80/4.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.80/4.03  thf(sk_C_type, type, sk_C: $i).
% 3.80/4.03  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 3.80/4.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.80/4.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.80/4.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.80/4.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.80/4.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.80/4.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.80/4.03  thf(t62_tops_2, conjecture,
% 3.80/4.03    (![A:$i]:
% 3.80/4.03     ( ( l1_struct_0 @ A ) =>
% 3.80/4.03       ( ![B:$i]:
% 3.80/4.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.80/4.03           ( ![C:$i]:
% 3.80/4.03             ( ( ( v1_funct_1 @ C ) & 
% 3.80/4.03                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.80/4.03                 ( m1_subset_1 @
% 3.80/4.03                   C @ 
% 3.80/4.03                   ( k1_zfmisc_1 @
% 3.80/4.03                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.80/4.03               ( ( ( ( k2_relset_1 @
% 3.80/4.03                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.80/4.03                     ( k2_struct_0 @ B ) ) & 
% 3.80/4.03                   ( v2_funct_1 @ C ) ) =>
% 3.80/4.03                 ( ( ( k1_relset_1 @
% 3.80/4.03                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.80/4.03                       ( k2_tops_2 @
% 3.80/4.03                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.80/4.03                     ( k2_struct_0 @ B ) ) & 
% 3.80/4.03                   ( ( k2_relset_1 @
% 3.80/4.03                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.80/4.03                       ( k2_tops_2 @
% 3.80/4.03                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.80/4.03                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 3.80/4.03  thf(zf_stmt_0, negated_conjecture,
% 3.80/4.03    (~( ![A:$i]:
% 3.80/4.03        ( ( l1_struct_0 @ A ) =>
% 3.80/4.03          ( ![B:$i]:
% 3.80/4.03            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.80/4.03              ( ![C:$i]:
% 3.80/4.03                ( ( ( v1_funct_1 @ C ) & 
% 3.80/4.03                    ( v1_funct_2 @
% 3.80/4.03                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.80/4.03                    ( m1_subset_1 @
% 3.80/4.03                      C @ 
% 3.80/4.03                      ( k1_zfmisc_1 @
% 3.80/4.03                        ( k2_zfmisc_1 @
% 3.80/4.03                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.80/4.03                  ( ( ( ( k2_relset_1 @
% 3.80/4.03                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.80/4.03                        ( k2_struct_0 @ B ) ) & 
% 3.80/4.03                      ( v2_funct_1 @ C ) ) =>
% 3.80/4.03                    ( ( ( k1_relset_1 @
% 3.80/4.03                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.80/4.03                          ( k2_tops_2 @
% 3.80/4.03                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.80/4.03                        ( k2_struct_0 @ B ) ) & 
% 3.80/4.03                      ( ( k2_relset_1 @
% 3.80/4.03                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.80/4.03                          ( k2_tops_2 @
% 3.80/4.03                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.80/4.03                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 3.80/4.03    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 3.80/4.03  thf('0', plain, (~ (v2_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('1', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf(redefinition_k2_relset_1, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.80/4.03  thf('2', plain,
% 3.80/4.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.80/4.03         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 3.80/4.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.80/4.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.80/4.03  thf('3', plain,
% 3.80/4.03      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.03         = (k2_relat_1 @ sk_C))),
% 3.80/4.03      inference('sup-', [status(thm)], ['1', '2'])).
% 3.80/4.03  thf('4', plain,
% 3.80/4.03      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.03         = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('5', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf(d3_struct_0, axiom,
% 3.80/4.03    (![A:$i]:
% 3.80/4.03     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.80/4.03  thf('6', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf(rc20_struct_0, axiom,
% 3.80/4.03    (![A:$i]:
% 3.80/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.80/4.03       ( ?[B:$i]:
% 3.80/4.03         ( ( v1_zfmisc_1 @ B ) & ( ~( v1_xboole_0 @ B ) ) & 
% 3.80/4.03           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.80/4.03  thf('7', plain,
% 3.80/4.03      (![X25 : $i]:
% 3.80/4.03         ((m1_subset_1 @ (sk_B @ X25) @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.80/4.03          | ~ (l1_struct_0 @ X25)
% 3.80/4.03          | (v2_struct_0 @ X25))),
% 3.80/4.03      inference('cnf', [status(esa)], [rc20_struct_0])).
% 3.80/4.03  thf('8', plain,
% 3.80/4.03      (![X0 : $i]:
% 3.80/4.03         ((m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 3.80/4.03          | ~ (l1_struct_0 @ X0)
% 3.80/4.03          | (v2_struct_0 @ X0)
% 3.80/4.03          | ~ (l1_struct_0 @ X0))),
% 3.80/4.03      inference('sup+', [status(thm)], ['6', '7'])).
% 3.80/4.03  thf('9', plain,
% 3.80/4.03      (![X0 : $i]:
% 3.80/4.03         ((v2_struct_0 @ X0)
% 3.80/4.03          | ~ (l1_struct_0 @ X0)
% 3.80/4.03          | (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 3.80/4.03      inference('simplify', [status(thm)], ['8'])).
% 3.80/4.03  thf('10', plain,
% 3.80/4.03      (((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_B_2)
% 3.80/4.03        | (v2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['5', '9'])).
% 3.80/4.03  thf('11', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('12', plain,
% 3.80/4.03      (((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 3.80/4.03        | (v2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('demod', [status(thm)], ['10', '11'])).
% 3.80/4.03  thf('13', plain, (~ (v2_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('14', plain,
% 3.80/4.03      ((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 3.80/4.03      inference('clc', [status(thm)], ['12', '13'])).
% 3.80/4.03  thf('15', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('16', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf(d1_funct_2, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.80/4.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.80/4.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.80/4.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.80/4.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.80/4.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.80/4.03  thf(zf_stmt_1, axiom,
% 3.80/4.03    (![B:$i,A:$i]:
% 3.80/4.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.80/4.03       ( zip_tseitin_0 @ B @ A ) ))).
% 3.80/4.03  thf('17', plain,
% 3.80/4.03      (![X16 : $i, X17 : $i]:
% 3.80/4.03         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.80/4.03  thf('18', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.80/4.03  thf(zf_stmt_3, axiom,
% 3.80/4.03    (![C:$i,B:$i,A:$i]:
% 3.80/4.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.80/4.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.80/4.03  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.80/4.03  thf(zf_stmt_5, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.80/4.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.80/4.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.80/4.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.80/4.03  thf('19', plain,
% 3.80/4.03      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.80/4.03         (~ (zip_tseitin_0 @ X21 @ X22)
% 3.80/4.03          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 3.80/4.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.80/4.03  thf('20', plain,
% 3.80/4.03      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 3.80/4.03        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['18', '19'])).
% 3.80/4.03  thf('21', plain,
% 3.80/4.03      ((((u1_struct_0 @ sk_B_2) = (k1_xboole_0))
% 3.80/4.03        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['17', '20'])).
% 3.80/4.03  thf('22', plain,
% 3.80/4.03      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('23', plain,
% 3.80/4.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.80/4.03         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 3.80/4.03          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 3.80/4.03          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.80/4.03  thf('24', plain,
% 3.80/4.03      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 3.80/4.03        | ((u1_struct_0 @ sk_A)
% 3.80/4.03            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03               sk_C)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['22', '23'])).
% 3.80/4.03  thf('25', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf(redefinition_k1_relset_1, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.80/4.03  thf('26', plain,
% 3.80/4.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.80/4.03         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 3.80/4.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.80/4.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.80/4.03  thf('27', plain,
% 3.80/4.03      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.03         = (k1_relat_1 @ sk_C))),
% 3.80/4.03      inference('sup-', [status(thm)], ['25', '26'])).
% 3.80/4.03  thf('28', plain,
% 3.80/4.03      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 3.80/4.03        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.80/4.03      inference('demod', [status(thm)], ['24', '27'])).
% 3.80/4.03  thf('29', plain,
% 3.80/4.03      ((((u1_struct_0 @ sk_B_2) = (k1_xboole_0))
% 3.80/4.03        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['21', '28'])).
% 3.80/4.03  thf('30', plain,
% 3.80/4.03      ((((k2_struct_0 @ sk_B_2) = (k1_xboole_0))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_B_2)
% 3.80/4.03        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.80/4.03      inference('sup+', [status(thm)], ['16', '29'])).
% 3.80/4.03  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('32', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('33', plain,
% 3.80/4.03      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 3.80/4.03        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.80/4.03      inference('demod', [status(thm)], ['30', '31', '32'])).
% 3.80/4.03  thf('34', plain,
% 3.80/4.03      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_A)
% 3.80/4.03        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 3.80/4.03      inference('sup+', [status(thm)], ['15', '33'])).
% 3.80/4.03  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('36', plain,
% 3.80/4.03      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.80/4.03        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 3.80/4.03      inference('demod', [status(thm)], ['34', '35'])).
% 3.80/4.03  thf('37', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('38', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('39', plain,
% 3.80/4.03      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03          != (k2_struct_0 @ sk_B_2))
% 3.80/4.03        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03            != (k2_struct_0 @ sk_A)))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('40', plain,
% 3.80/4.03      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03          != (k2_struct_0 @ sk_A)))
% 3.80/4.03         <= (~
% 3.80/4.03             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03                 sk_C))
% 3.80/4.03                = (k2_struct_0 @ sk_A))))),
% 3.80/4.03      inference('split', [status(esa)], ['39'])).
% 3.80/4.03  thf('41', plain,
% 3.80/4.03      (((((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03           != (k2_struct_0 @ sk_A))
% 3.80/4.03         | ~ (l1_struct_0 @ sk_B_2)))
% 3.80/4.03         <= (~
% 3.80/4.03             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03                 sk_C))
% 3.80/4.03                = (k2_struct_0 @ sk_A))))),
% 3.80/4.03      inference('sup-', [status(thm)], ['38', '40'])).
% 3.80/4.03  thf('42', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('43', plain,
% 3.80/4.03      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03          != (k2_struct_0 @ sk_A)))
% 3.80/4.03         <= (~
% 3.80/4.03             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03                 sk_C))
% 3.80/4.03                = (k2_struct_0 @ sk_A))))),
% 3.80/4.03      inference('demod', [status(thm)], ['41', '42'])).
% 3.80/4.03  thf('44', plain,
% 3.80/4.03      (((((k2_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03           != (k2_struct_0 @ sk_A))
% 3.80/4.03         | ~ (l1_struct_0 @ sk_B_2)))
% 3.80/4.03         <= (~
% 3.80/4.03             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03                 sk_C))
% 3.80/4.03                = (k2_struct_0 @ sk_A))))),
% 3.80/4.03      inference('sup-', [status(thm)], ['37', '43'])).
% 3.80/4.03  thf('45', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('46', plain,
% 3.80/4.03      ((((k2_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.03          != (k2_struct_0 @ sk_A)))
% 3.80/4.03         <= (~
% 3.80/4.03             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03                 sk_C))
% 3.80/4.03                = (k2_struct_0 @ sk_A))))),
% 3.80/4.03      inference('demod', [status(thm)], ['44', '45'])).
% 3.80/4.03  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('49', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('50', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('51', plain,
% 3.80/4.03      (((m1_subset_1 @ sk_C @ 
% 3.80/4.03         (k1_zfmisc_1 @ 
% 3.80/4.03          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['49', '50'])).
% 3.80/4.03  thf('52', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('53', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('demod', [status(thm)], ['51', '52'])).
% 3.80/4.03  thf('54', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('55', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.03      inference('demod', [status(thm)], ['53', '54'])).
% 3.80/4.03  thf(d4_tops_2, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/4.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/4.03       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.80/4.03         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.80/4.03  thf('56', plain,
% 3.80/4.03      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.80/4.03         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 3.80/4.03          | ~ (v2_funct_1 @ X31)
% 3.80/4.03          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 3.80/4.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 3.80/4.03          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 3.80/4.03          | ~ (v1_funct_1 @ X31))),
% 3.80/4.03      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.80/4.03  thf('57', plain,
% 3.80/4.03      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.03        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 3.80/4.03        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.03            = (k2_funct_1 @ sk_C))
% 3.80/4.03        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.03        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.03            != (k2_relat_1 @ sk_C)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['55', '56'])).
% 3.80/4.03  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('59', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('60', plain,
% 3.80/4.03      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('61', plain,
% 3.80/4.03      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['59', '60'])).
% 3.80/4.03  thf('62', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('63', plain,
% 3.80/4.03      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('demod', [status(thm)], ['61', '62'])).
% 3.80/4.03  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('65', plain,
% 3.80/4.03      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.80/4.03      inference('demod', [status(thm)], ['63', '64'])).
% 3.80/4.03  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('67', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('68', plain,
% 3.80/4.03      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.03         = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('69', plain,
% 3.80/4.03      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.03          = (k2_struct_0 @ sk_B_2))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['67', '68'])).
% 3.80/4.03  thf('70', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('71', plain,
% 3.80/4.03      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.03         = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('demod', [status(thm)], ['69', '70'])).
% 3.80/4.03  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.03      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.03  thf('74', plain,
% 3.80/4.03      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.03         = (k2_relat_1 @ sk_C))),
% 3.80/4.03      inference('demod', [status(thm)], ['71', '72', '73'])).
% 3.80/4.03  thf('75', plain,
% 3.80/4.03      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.03          = (k2_funct_1 @ sk_C))
% 3.80/4.03        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.80/4.03      inference('demod', [status(thm)], ['57', '58', '65', '66', '74'])).
% 3.80/4.03  thf('76', plain,
% 3.80/4.03      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.03         = (k2_funct_1 @ sk_C))),
% 3.80/4.03      inference('simplify', [status(thm)], ['75'])).
% 3.80/4.03  thf('77', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.03      inference('demod', [status(thm)], ['53', '54'])).
% 3.80/4.03  thf(dt_k2_tops_2, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/4.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/4.03       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 3.80/4.03         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 3.80/4.03         ( m1_subset_1 @
% 3.80/4.03           ( k2_tops_2 @ A @ B @ C ) @ 
% 3.80/4.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 3.80/4.03  thf('78', plain,
% 3.80/4.03      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.80/4.03         ((m1_subset_1 @ (k2_tops_2 @ X32 @ X33 @ X34) @ 
% 3.80/4.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.80/4.03          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.80/4.03          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 3.80/4.03          | ~ (v1_funct_1 @ X34))),
% 3.80/4.03      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 3.80/4.03  thf('79', plain,
% 3.80/4.03      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.03        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 3.80/4.03        | (m1_subset_1 @ 
% 3.80/4.03           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 3.80/4.03           (k1_zfmisc_1 @ 
% 3.80/4.03            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 3.80/4.03      inference('sup-', [status(thm)], ['77', '78'])).
% 3.80/4.03  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('81', plain,
% 3.80/4.03      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.80/4.03      inference('demod', [status(thm)], ['63', '64'])).
% 3.80/4.03  thf('82', plain,
% 3.80/4.03      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.03         = (k2_funct_1 @ sk_C))),
% 3.80/4.03      inference('simplify', [status(thm)], ['75'])).
% 3.80/4.03  thf('83', plain,
% 3.80/4.03      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.80/4.03      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 3.80/4.03  thf('84', plain,
% 3.80/4.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.80/4.03         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 3.80/4.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.80/4.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.80/4.03  thf('85', plain,
% 3.80/4.03      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['83', '84'])).
% 3.80/4.03  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf(t55_funct_1, axiom,
% 3.80/4.03    (![A:$i]:
% 3.80/4.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.80/4.03       ( ( v2_funct_1 @ A ) =>
% 3.80/4.03         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.80/4.03           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.80/4.03  thf('87', plain,
% 3.80/4.03      (![X6 : $i]:
% 3.80/4.03         (~ (v2_funct_1 @ X6)
% 3.80/4.03          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 3.80/4.03          | ~ (v1_funct_1 @ X6)
% 3.80/4.03          | ~ (v1_relat_1 @ X6))),
% 3.80/4.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.80/4.03  thf('88', plain,
% 3.80/4.03      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.03        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.03        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.03      inference('sup-', [status(thm)], ['86', '87'])).
% 3.80/4.03  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('90', plain,
% 3.80/4.03      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.03        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.03      inference('demod', [status(thm)], ['88', '89'])).
% 3.80/4.03  thf('91', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf(cc1_relset_1, axiom,
% 3.80/4.03    (![A:$i,B:$i,C:$i]:
% 3.80/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.03       ( v1_relat_1 @ C ) ))).
% 3.80/4.03  thf('92', plain,
% 3.80/4.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.80/4.03         ((v1_relat_1 @ X7)
% 3.80/4.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.80/4.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.80/4.03  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.03      inference('sup-', [status(thm)], ['91', '92'])).
% 3.80/4.03  thf('94', plain,
% 3.80/4.03      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.03      inference('demod', [status(thm)], ['90', '93'])).
% 3.80/4.03  thf('95', plain,
% 3.80/4.03      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 3.80/4.03      inference('demod', [status(thm)], ['85', '94'])).
% 3.80/4.03  thf('96', plain,
% 3.80/4.03      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 3.80/4.03         <= (~
% 3.80/4.03             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.03                 sk_C))
% 3.80/4.03                = (k2_struct_0 @ sk_A))))),
% 3.80/4.03      inference('demod', [status(thm)], ['46', '47', '48', '76', '95'])).
% 3.80/4.03  thf('97', plain,
% 3.80/4.03      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.80/4.03      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 3.80/4.03  thf('98', plain,
% 3.80/4.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.80/4.03         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 3.80/4.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.80/4.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.80/4.03  thf('99', plain,
% 3.80/4.03      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.03      inference('sup-', [status(thm)], ['97', '98'])).
% 3.80/4.03  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('101', plain,
% 3.80/4.03      (![X6 : $i]:
% 3.80/4.03         (~ (v2_funct_1 @ X6)
% 3.80/4.03          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 3.80/4.03          | ~ (v1_funct_1 @ X6)
% 3.80/4.03          | ~ (v1_relat_1 @ X6))),
% 3.80/4.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.80/4.03  thf('102', plain,
% 3.80/4.03      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.03        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.03        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.03      inference('sup-', [status(thm)], ['100', '101'])).
% 3.80/4.03  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('104', plain,
% 3.80/4.03      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.03        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.03      inference('demod', [status(thm)], ['102', '103'])).
% 3.80/4.03  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.03      inference('sup-', [status(thm)], ['91', '92'])).
% 3.80/4.03  thf('106', plain,
% 3.80/4.03      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.03      inference('demod', [status(thm)], ['104', '105'])).
% 3.80/4.03  thf('107', plain,
% 3.80/4.03      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.03         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 3.80/4.03      inference('demod', [status(thm)], ['99', '106'])).
% 3.80/4.03  thf('108', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('109', plain,
% 3.80/4.03      (![X24 : $i]:
% 3.80/4.03         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.03  thf('110', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('111', plain,
% 3.80/4.03      (((m1_subset_1 @ sk_C @ 
% 3.80/4.03         (k1_zfmisc_1 @ 
% 3.80/4.03          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 3.80/4.03        | ~ (l1_struct_0 @ sk_A))),
% 3.80/4.03      inference('sup+', [status(thm)], ['109', '110'])).
% 3.80/4.03  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.03  thf('113', plain,
% 3.80/4.03      ((m1_subset_1 @ sk_C @ 
% 3.80/4.03        (k1_zfmisc_1 @ 
% 3.80/4.03         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 3.80/4.03      inference('demod', [status(thm)], ['111', '112'])).
% 3.80/4.03  thf('114', plain,
% 3.80/4.03      (((m1_subset_1 @ sk_C @ 
% 3.80/4.04         (k1_zfmisc_1 @ 
% 3.80/4.04          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))
% 3.80/4.04        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['108', '113'])).
% 3.80/4.04  thf('115', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('116', plain,
% 3.80/4.04      ((m1_subset_1 @ sk_C @ 
% 3.80/4.04        (k1_zfmisc_1 @ 
% 3.80/4.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('demod', [status(thm)], ['114', '115'])).
% 3.80/4.04  thf('117', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('118', plain,
% 3.80/4.04      ((m1_subset_1 @ sk_C @ 
% 3.80/4.04        (k1_zfmisc_1 @ 
% 3.80/4.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.04      inference('demod', [status(thm)], ['116', '117'])).
% 3.80/4.04  thf('119', plain,
% 3.80/4.04      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.80/4.04         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 3.80/4.04          | ~ (v2_funct_1 @ X31)
% 3.80/4.04          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 3.80/4.04          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 3.80/4.04          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 3.80/4.04          | ~ (v1_funct_1 @ X31))),
% 3.80/4.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.80/4.04  thf('120', plain,
% 3.80/4.04      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 3.80/4.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.04            = (k2_funct_1 @ sk_C))
% 3.80/4.04        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.04        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.04            != (k2_relat_1 @ sk_C)))),
% 3.80/4.04      inference('sup-', [status(thm)], ['118', '119'])).
% 3.80/4.04  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('122', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('123', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('124', plain,
% 3.80/4.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('125', plain,
% 3.80/4.04      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 3.80/4.04        | ~ (l1_struct_0 @ sk_A))),
% 3.80/4.04      inference('sup+', [status(thm)], ['123', '124'])).
% 3.80/4.04  thf('126', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('127', plain,
% 3.80/4.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('demod', [status(thm)], ['125', '126'])).
% 3.80/4.04  thf('128', plain,
% 3.80/4.04      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 3.80/4.04        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['122', '127'])).
% 3.80/4.04  thf('129', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('130', plain,
% 3.80/4.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('demod', [status(thm)], ['128', '129'])).
% 3.80/4.04  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('132', plain,
% 3.80/4.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.80/4.04      inference('demod', [status(thm)], ['130', '131'])).
% 3.80/4.04  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('134', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('135', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('136', plain,
% 3.80/4.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.04         = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('137', plain,
% 3.80/4.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.04          = (k2_struct_0 @ sk_B_2))
% 3.80/4.04        | ~ (l1_struct_0 @ sk_A))),
% 3.80/4.04      inference('sup+', [status(thm)], ['135', '136'])).
% 3.80/4.04  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('139', plain,
% 3.80/4.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.04         = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('demod', [status(thm)], ['137', '138'])).
% 3.80/4.04  thf('140', plain,
% 3.80/4.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.04          = (k2_struct_0 @ sk_B_2))
% 3.80/4.04        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['134', '139'])).
% 3.80/4.04  thf('141', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('142', plain,
% 3.80/4.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 3.80/4.04         = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('demod', [status(thm)], ['140', '141'])).
% 3.80/4.04  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('144', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('145', plain,
% 3.80/4.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.04         = (k2_relat_1 @ sk_C))),
% 3.80/4.04      inference('demod', [status(thm)], ['142', '143', '144'])).
% 3.80/4.04  thf('146', plain,
% 3.80/4.04      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.04          = (k2_funct_1 @ sk_C))
% 3.80/4.04        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.80/4.04      inference('demod', [status(thm)], ['120', '121', '132', '133', '145'])).
% 3.80/4.04  thf('147', plain,
% 3.80/4.04      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.04         = (k2_funct_1 @ sk_C))),
% 3.80/4.04      inference('simplify', [status(thm)], ['146'])).
% 3.80/4.04  thf('148', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('149', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('150', plain,
% 3.80/4.04      (![X24 : $i]:
% 3.80/4.04         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.04  thf('151', plain,
% 3.80/4.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          != (k2_struct_0 @ sk_B_2)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('split', [status(esa)], ['39'])).
% 3.80/4.04  thf('152', plain,
% 3.80/4.04      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04           != (k2_struct_0 @ sk_B_2))
% 3.80/4.04         | ~ (l1_struct_0 @ sk_B_2)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('sup-', [status(thm)], ['150', '151'])).
% 3.80/4.04  thf('153', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('154', plain,
% 3.80/4.04      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          != (k2_struct_0 @ sk_B_2)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('demod', [status(thm)], ['152', '153'])).
% 3.80/4.04  thf('155', plain,
% 3.80/4.04      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04           != (k2_struct_0 @ sk_B_2))
% 3.80/4.04         | ~ (l1_struct_0 @ sk_A)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('sup-', [status(thm)], ['149', '154'])).
% 3.80/4.04  thf('156', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('157', plain,
% 3.80/4.04      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          != (k2_struct_0 @ sk_B_2)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('demod', [status(thm)], ['155', '156'])).
% 3.80/4.04  thf('158', plain,
% 3.80/4.04      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04           != (k2_struct_0 @ sk_B_2))
% 3.80/4.04         | ~ (l1_struct_0 @ sk_B_2)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('sup-', [status(thm)], ['148', '157'])).
% 3.80/4.04  thf('159', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('160', plain,
% 3.80/4.04      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          != (k2_struct_0 @ sk_B_2)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('demod', [status(thm)], ['158', '159'])).
% 3.80/4.04  thf('161', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('162', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('163', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup+', [status(thm)], ['3', '4'])).
% 3.80/4.04  thf('164', plain,
% 3.80/4.04      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.80/4.04          != (k2_relat_1 @ sk_C)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 3.80/4.04  thf('165', plain,
% 3.80/4.04      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('sup-', [status(thm)], ['147', '164'])).
% 3.80/4.04  thf('166', plain,
% 3.80/4.04      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 3.80/4.04         <= (~
% 3.80/4.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 3.80/4.04                 sk_C))
% 3.80/4.04                = (k2_struct_0 @ sk_B_2))))),
% 3.80/4.04      inference('sup-', [status(thm)], ['107', '165'])).
% 3.80/4.04  thf('167', plain,
% 3.80/4.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          = (k2_struct_0 @ sk_B_2)))),
% 3.80/4.04      inference('simplify', [status(thm)], ['166'])).
% 3.80/4.04  thf('168', plain,
% 3.80/4.04      (~
% 3.80/4.04       (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          = (k2_struct_0 @ sk_A))) | 
% 3.80/4.04       ~
% 3.80/4.04       (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          = (k2_struct_0 @ sk_B_2)))),
% 3.80/4.04      inference('split', [status(esa)], ['39'])).
% 3.80/4.04  thf('169', plain,
% 3.80/4.04      (~
% 3.80/4.04       (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 3.80/4.04          = (k2_struct_0 @ sk_A)))),
% 3.80/4.04      inference('sat_resolution*', [status(thm)], ['167', '168'])).
% 3.80/4.04  thf('170', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 3.80/4.04      inference('simpl_trail', [status(thm)], ['96', '169'])).
% 3.80/4.04  thf('171', plain,
% 3.80/4.04      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 3.80/4.04      inference('sup-', [status(thm)], ['36', '170'])).
% 3.80/4.04  thf('172', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 3.80/4.04      inference('simplify', [status(thm)], ['171'])).
% 3.80/4.04  thf('173', plain,
% 3.80/4.04      ((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.80/4.04      inference('demod', [status(thm)], ['14', '172'])).
% 3.80/4.04  thf(t2_subset, axiom,
% 3.80/4.04    (![A:$i,B:$i]:
% 3.80/4.04     ( ( m1_subset_1 @ A @ B ) =>
% 3.80/4.04       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.80/4.04  thf('174', plain,
% 3.80/4.04      (![X4 : $i, X5 : $i]:
% 3.80/4.04         ((r2_hidden @ X4 @ X5)
% 3.80/4.04          | (v1_xboole_0 @ X5)
% 3.80/4.04          | ~ (m1_subset_1 @ X4 @ X5))),
% 3.80/4.04      inference('cnf', [status(esa)], [t2_subset])).
% 3.80/4.04  thf('175', plain,
% 3.80/4.04      (((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.80/4.04        | (r2_hidden @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 3.80/4.04      inference('sup-', [status(thm)], ['173', '174'])).
% 3.80/4.04  thf(fc1_subset_1, axiom,
% 3.80/4.04    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.80/4.04  thf('176', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 3.80/4.04      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.80/4.04  thf('177', plain,
% 3.80/4.04      ((r2_hidden @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.80/4.04      inference('clc', [status(thm)], ['175', '176'])).
% 3.80/4.04  thf(t99_zfmisc_1, axiom,
% 3.80/4.04    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 3.80/4.04  thf('178', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 3.80/4.04      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 3.80/4.04  thf(t91_orders_1, axiom,
% 3.80/4.04    (![A:$i]:
% 3.80/4.04     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 3.80/4.04            ( ![B:$i]:
% 3.80/4.04              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 3.80/4.04       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 3.80/4.04            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 3.80/4.04  thf('179', plain,
% 3.80/4.04      (![X26 : $i, X27 : $i]:
% 3.80/4.04         (((X26) = (k1_xboole_0))
% 3.80/4.04          | ~ (r2_hidden @ X26 @ X27)
% 3.80/4.04          | ((k3_tarski @ X27) != (k1_xboole_0)))),
% 3.80/4.04      inference('cnf', [status(esa)], [t91_orders_1])).
% 3.80/4.04  thf('180', plain,
% 3.80/4.04      (![X0 : $i, X1 : $i]:
% 3.80/4.04         (((X0) != (k1_xboole_0))
% 3.80/4.04          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 3.80/4.04          | ((X1) = (k1_xboole_0)))),
% 3.80/4.04      inference('sup-', [status(thm)], ['178', '179'])).
% 3.80/4.04  thf('181', plain,
% 3.80/4.04      (![X1 : $i]:
% 3.80/4.04         (((X1) = (k1_xboole_0))
% 3.80/4.04          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 3.80/4.04      inference('simplify', [status(thm)], ['180'])).
% 3.80/4.04  thf('182', plain, (((sk_B @ sk_B_2) = (k1_xboole_0))),
% 3.80/4.04      inference('sup-', [status(thm)], ['177', '181'])).
% 3.80/4.04  thf('183', plain,
% 3.80/4.04      (![X25 : $i]:
% 3.80/4.04         (~ (v1_xboole_0 @ (sk_B @ X25))
% 3.80/4.04          | ~ (l1_struct_0 @ X25)
% 3.80/4.04          | (v2_struct_0 @ X25))),
% 3.80/4.04      inference('cnf', [status(esa)], [rc20_struct_0])).
% 3.80/4.04  thf('184', plain,
% 3.80/4.04      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.80/4.04        | (v2_struct_0 @ sk_B_2)
% 3.80/4.04        | ~ (l1_struct_0 @ sk_B_2))),
% 3.80/4.04      inference('sup-', [status(thm)], ['182', '183'])).
% 3.80/4.04  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 3.80/4.04  thf('185', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 3.80/4.04      inference('cnf', [status(esa)], [d3_subset_1])).
% 3.80/4.04  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 3.80/4.04  thf('186', plain, (![X2 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X2))),
% 3.80/4.04      inference('cnf', [status(esa)], [fc13_subset_1])).
% 3.80/4.04  thf('187', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.80/4.04      inference('sup+', [status(thm)], ['185', '186'])).
% 3.80/4.04  thf('188', plain, ((l1_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.04  thf('189', plain, ((v2_struct_0 @ sk_B_2)),
% 3.80/4.04      inference('demod', [status(thm)], ['184', '187', '188'])).
% 3.80/4.04  thf('190', plain, ($false), inference('demod', [status(thm)], ['0', '189'])).
% 3.80/4.04  
% 3.80/4.04  % SZS output end Refutation
% 3.80/4.04  
% 3.80/4.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
