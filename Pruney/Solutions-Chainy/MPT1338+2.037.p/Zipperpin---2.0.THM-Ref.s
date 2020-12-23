%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o2hvJbUNQg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:53 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  260 (1291 expanded)
%              Number of leaves         :   50 ( 397 expanded)
%              Depth                    :   22
%              Number of atoms          : 2354 (31248 expanded)
%              Number of equality atoms :  179 (1732 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('29',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(rc20_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('43',plain,(
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

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X28 )
      | ( ( k3_tarski @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k1_subset_1 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['50','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','57','58'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('64',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
     != ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('70',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('72',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('75',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('85',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X33 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('96',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('108',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','108'])).

thf('110',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87','94','110'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('113',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
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

thf('117',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('122',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','123'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','124'])).

thf('126',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10','60','61','77','125','130'])).

thf('132',plain,
    ( $false
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('134',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('135',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','142'])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('145',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['145','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('160',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['159','164'])).

thf('166',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('173',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['171','176'])).

thf('178',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('181',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('182',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','169','170','182'])).

thf('184',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('186',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('188',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('189',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['185','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('199',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('201',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['184','201'])).

thf('203',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['144','202'])).

thf('204',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['143','203'])).

thf('205',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('207',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['205','206'])).

thf('208',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['132','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o2hvJbUNQg
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.29/1.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.49  % Solved by: fo/fo7.sh
% 1.29/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.49  % done 750 iterations in 1.031s
% 1.29/1.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.49  % SZS output start Refutation
% 1.29/1.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.29/1.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.29/1.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.29/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.29/1.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.29/1.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.29/1.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.29/1.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.29/1.49  thf(sk_C_type, type, sk_C: $i).
% 1.29/1.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.29/1.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.29/1.49  thf(sk_B_type, type, sk_B: $i > $i).
% 1.29/1.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.29/1.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.29/1.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.29/1.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.29/1.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.29/1.49  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.29/1.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.29/1.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.29/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.29/1.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.29/1.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.29/1.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.29/1.49  thf(d3_struct_0, axiom,
% 1.29/1.49    (![A:$i]:
% 1.29/1.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.29/1.49  thf('0', plain,
% 1.29/1.49      (![X25 : $i]:
% 1.29/1.49         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.49  thf(t62_tops_2, conjecture,
% 1.29/1.49    (![A:$i]:
% 1.29/1.49     ( ( l1_struct_0 @ A ) =>
% 1.29/1.49       ( ![B:$i]:
% 1.29/1.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.29/1.49           ( ![C:$i]:
% 1.29/1.49             ( ( ( v1_funct_1 @ C ) & 
% 1.29/1.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.49                 ( m1_subset_1 @
% 1.29/1.49                   C @ 
% 1.29/1.49                   ( k1_zfmisc_1 @
% 1.29/1.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.49               ( ( ( ( k2_relset_1 @
% 1.29/1.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.29/1.49                     ( k2_struct_0 @ B ) ) & 
% 1.29/1.49                   ( v2_funct_1 @ C ) ) =>
% 1.29/1.49                 ( ( ( k1_relset_1 @
% 1.29/1.49                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.49                       ( k2_tops_2 @
% 1.29/1.49                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.49                     ( k2_struct_0 @ B ) ) & 
% 1.29/1.49                   ( ( k2_relset_1 @
% 1.29/1.49                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.49                       ( k2_tops_2 @
% 1.29/1.49                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.49                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.29/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.49    (~( ![A:$i]:
% 1.29/1.49        ( ( l1_struct_0 @ A ) =>
% 1.29/1.49          ( ![B:$i]:
% 1.29/1.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.29/1.49              ( ![C:$i]:
% 1.29/1.49                ( ( ( v1_funct_1 @ C ) & 
% 1.29/1.49                    ( v1_funct_2 @
% 1.29/1.49                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.49                    ( m1_subset_1 @
% 1.29/1.49                      C @ 
% 1.29/1.49                      ( k1_zfmisc_1 @
% 1.29/1.49                        ( k2_zfmisc_1 @
% 1.29/1.49                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.49                  ( ( ( ( k2_relset_1 @
% 1.29/1.49                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.29/1.49                        ( k2_struct_0 @ B ) ) & 
% 1.29/1.49                      ( v2_funct_1 @ C ) ) =>
% 1.29/1.49                    ( ( ( k1_relset_1 @
% 1.29/1.49                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.49                          ( k2_tops_2 @
% 1.29/1.49                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.49                        ( k2_struct_0 @ B ) ) & 
% 1.29/1.49                      ( ( k2_relset_1 @
% 1.29/1.49                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.29/1.49                          ( k2_tops_2 @
% 1.29/1.49                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.29/1.49                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.29/1.49    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.29/1.49  thf('1', plain,
% 1.29/1.49      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.49          != (k2_struct_0 @ sk_B_2))
% 1.29/1.49        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.49            != (k2_struct_0 @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('2', plain,
% 1.29/1.49      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.49          != (k2_struct_0 @ sk_A)))
% 1.29/1.49         <= (~
% 1.29/1.49             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.49                 sk_C))
% 1.29/1.49                = (k2_struct_0 @ sk_A))))),
% 1.29/1.49      inference('split', [status(esa)], ['1'])).
% 1.29/1.49  thf('3', plain,
% 1.29/1.49      (((((k2_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.49           != (k2_struct_0 @ sk_A))
% 1.29/1.49         | ~ (l1_struct_0 @ sk_B_2)))
% 1.29/1.49         <= (~
% 1.29/1.49             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.49                 sk_C))
% 1.29/1.49                = (k2_struct_0 @ sk_A))))),
% 1.29/1.49      inference('sup-', [status(thm)], ['0', '2'])).
% 1.29/1.49  thf('4', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('5', plain,
% 1.29/1.49      ((((k2_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.49          != (k2_struct_0 @ sk_A)))
% 1.29/1.49         <= (~
% 1.29/1.49             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.49                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.49                 sk_C))
% 1.29/1.49                = (k2_struct_0 @ sk_A))))),
% 1.29/1.49      inference('demod', [status(thm)], ['3', '4'])).
% 1.29/1.49  thf('6', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ 
% 1.29/1.49        (k1_zfmisc_1 @ 
% 1.29/1.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(redefinition_k2_relset_1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.29/1.49  thf('7', plain,
% 1.29/1.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.29/1.49         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.29/1.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.29/1.49  thf('8', plain,
% 1.29/1.49      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.49         = (k2_relat_1 @ sk_C))),
% 1.29/1.49      inference('sup-', [status(thm)], ['6', '7'])).
% 1.29/1.49  thf('9', plain,
% 1.29/1.49      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.49         = (k2_struct_0 @ sk_B_2))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('10', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.49      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.49  thf('11', plain,
% 1.29/1.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(d1_funct_2, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.29/1.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.29/1.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.29/1.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.29/1.49  thf(zf_stmt_1, axiom,
% 1.29/1.49    (![C:$i,B:$i,A:$i]:
% 1.29/1.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.29/1.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.29/1.49  thf('12', plain,
% 1.29/1.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.29/1.49         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.29/1.49          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.29/1.49          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.49  thf('13', plain,
% 1.29/1.49      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 1.29/1.49        | ((u1_struct_0 @ sk_A)
% 1.29/1.49            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.49               sk_C)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['11', '12'])).
% 1.29/1.49  thf('14', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ 
% 1.29/1.49        (k1_zfmisc_1 @ 
% 1.29/1.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(redefinition_k1_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.29/1.50  thf('15', plain,
% 1.29/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.29/1.50         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.29/1.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.50  thf('16', plain,
% 1.29/1.50      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.50  thf('17', plain,
% 1.29/1.50      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 1.29/1.50        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['13', '16'])).
% 1.29/1.50  thf('18', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('19', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('20', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.29/1.50  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.29/1.50  thf(zf_stmt_4, axiom,
% 1.29/1.50    (![B:$i,A:$i]:
% 1.29/1.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.50       ( zip_tseitin_0 @ B @ A ) ))).
% 1.29/1.50  thf(zf_stmt_5, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.29/1.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.29/1.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.29/1.50  thf('21', plain,
% 1.29/1.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.29/1.50         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.29/1.50          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.29/1.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.29/1.50  thf('22', plain,
% 1.29/1.50      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 1.29/1.50        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['20', '21'])).
% 1.29/1.50  thf('23', plain,
% 1.29/1.50      ((~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A)
% 1.29/1.50        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['19', '22'])).
% 1.29/1.50  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('25', plain,
% 1.29/1.50      ((~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.29/1.50        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.50      inference('demod', [status(thm)], ['23', '24'])).
% 1.29/1.50  thf('26', plain,
% 1.29/1.50      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2)
% 1.29/1.50        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['18', '25'])).
% 1.29/1.50  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('29', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf(rc20_struct_0, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.29/1.50       ( ?[B:$i]:
% 1.29/1.50         ( ( v1_zfmisc_1 @ B ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.29/1.50           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.29/1.50  thf('30', plain,
% 1.29/1.50      (![X26 : $i]:
% 1.29/1.50         ((m1_subset_1 @ (sk_B @ X26) @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.29/1.50          | ~ (l1_struct_0 @ X26)
% 1.29/1.50          | (v2_struct_0 @ X26))),
% 1.29/1.50      inference('cnf', [status(esa)], [rc20_struct_0])).
% 1.29/1.50  thf('31', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.29/1.50          | ~ (l1_struct_0 @ X0)
% 1.29/1.50          | (v2_struct_0 @ X0)
% 1.29/1.50          | ~ (l1_struct_0 @ X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['29', '30'])).
% 1.29/1.50  thf('32', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((v2_struct_0 @ X0)
% 1.29/1.50          | ~ (l1_struct_0 @ X0)
% 1.29/1.50          | (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.29/1.50      inference('simplify', [status(thm)], ['31'])).
% 1.29/1.50  thf('33', plain,
% 1.29/1.50      (((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2)
% 1.29/1.50        | (v2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['28', '32'])).
% 1.29/1.50  thf('34', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('35', plain,
% 1.29/1.50      (((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 1.29/1.50        | (v2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['33', '34'])).
% 1.29/1.50  thf('36', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('37', plain,
% 1.29/1.50      ((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('clc', [status(thm)], ['35', '36'])).
% 1.29/1.50  thf(d2_subset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i]:
% 1.29/1.50     ( ( ( v1_xboole_0 @ A ) =>
% 1.29/1.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.29/1.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.29/1.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.29/1.50  thf('38', plain,
% 1.29/1.50      (![X1 : $i, X2 : $i]:
% 1.29/1.50         (~ (m1_subset_1 @ X1 @ X2)
% 1.29/1.50          | (r2_hidden @ X1 @ X2)
% 1.29/1.50          | (v1_xboole_0 @ X2))),
% 1.29/1.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.29/1.50  thf('39', plain,
% 1.29/1.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 1.29/1.50        | (r2_hidden @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['37', '38'])).
% 1.29/1.50  thf(fc1_subset_1, axiom,
% 1.29/1.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.29/1.50  thf('40', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.29/1.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.29/1.50  thf('41', plain,
% 1.29/1.50      ((r2_hidden @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('clc', [status(thm)], ['39', '40'])).
% 1.29/1.50  thf('42', plain,
% 1.29/1.50      (![X17 : $i, X18 : $i]:
% 1.29/1.50         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.29/1.50  thf(t99_zfmisc_1, axiom,
% 1.29/1.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.29/1.50  thf('43', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 1.29/1.50      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.29/1.50  thf(t91_orders_1, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 1.29/1.50            ( ![B:$i]:
% 1.29/1.50              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 1.29/1.50       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 1.29/1.50            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.29/1.50  thf('44', plain,
% 1.29/1.50      (![X27 : $i, X28 : $i]:
% 1.29/1.50         (((X27) = (k1_xboole_0))
% 1.29/1.50          | ~ (r2_hidden @ X27 @ X28)
% 1.29/1.50          | ((k3_tarski @ X28) != (k1_xboole_0)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t91_orders_1])).
% 1.29/1.50  thf('45', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         (((X0) != (k1_xboole_0))
% 1.29/1.50          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 1.29/1.50          | ((X1) = (k1_xboole_0)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['43', '44'])).
% 1.29/1.50  thf('46', plain,
% 1.29/1.50      (![X1 : $i]:
% 1.29/1.50         (((X1) = (k1_xboole_0))
% 1.29/1.50          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.29/1.50      inference('simplify', [status(thm)], ['45'])).
% 1.29/1.50  thf('47', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         (~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 1.29/1.50          | (zip_tseitin_0 @ X0 @ X2)
% 1.29/1.50          | ((X1) = (k1_xboole_0)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['42', '46'])).
% 1.29/1.50  thf('48', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         (((sk_B @ sk_B_2) = (k1_xboole_0))
% 1.29/1.50          | (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['41', '47'])).
% 1.29/1.50  thf('49', plain,
% 1.29/1.50      (![X26 : $i]:
% 1.29/1.50         (~ (v1_xboole_0 @ (sk_B @ X26))
% 1.29/1.50          | ~ (l1_struct_0 @ X26)
% 1.29/1.50          | (v2_struct_0 @ X26))),
% 1.29/1.50      inference('cnf', [status(esa)], [rc20_struct_0])).
% 1.29/1.50  thf('50', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.29/1.50          | (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 1.29/1.50          | (v2_struct_0 @ sk_B_2)
% 1.29/1.50          | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup-', [status(thm)], ['48', '49'])).
% 1.29/1.50  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.29/1.50  thf('51', plain, (![X4 : $i]: ((k1_subset_1 @ X4) = (k1_xboole_0))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.29/1.50  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 1.29/1.50  thf('52', plain, (![X5 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X5))),
% 1.29/1.50      inference('cnf', [status(esa)], [fc13_subset_1])).
% 1.29/1.50  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.29/1.50      inference('sup+', [status(thm)], ['51', '52'])).
% 1.29/1.50  thf('54', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('55', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0) | (v2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['50', '53', '54'])).
% 1.29/1.50  thf('56', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('57', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)),
% 1.29/1.50      inference('clc', [status(thm)], ['55', '56'])).
% 1.29/1.50  thf('58', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('59', plain,
% 1.29/1.50      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['26', '27', '57', '58'])).
% 1.29/1.50  thf('60', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['17', '59'])).
% 1.29/1.50  thf('61', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['17', '59'])).
% 1.29/1.50  thf('62', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('63', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(d4_tops_2, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.50       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.29/1.50         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.29/1.50  thf('64', plain,
% 1.29/1.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 1.29/1.50          | ~ (v2_funct_1 @ X32)
% 1.29/1.50          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 1.29/1.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.29/1.50          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.29/1.50          | ~ (v1_funct_1 @ X32))),
% 1.29/1.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.29/1.50  thf('65', plain,
% 1.29/1.50      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 1.29/1.50        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C)
% 1.29/1.50        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50            != (u1_struct_0 @ sk_B_2)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['63', '64'])).
% 1.29/1.50  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('67', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('69', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['6', '7'])).
% 1.29/1.50  thf('70', plain,
% 1.29/1.50      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50          = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B_2)))),
% 1.29/1.50      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.29/1.50  thf('71', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['17', '59'])).
% 1.29/1.50  thf('72', plain,
% 1.29/1.50      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50          = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B_2)))),
% 1.29/1.50      inference('demod', [status(thm)], ['70', '71'])).
% 1.29/1.50  thf('73', plain,
% 1.29/1.50      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2)
% 1.29/1.50        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['62', '72'])).
% 1.29/1.50  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('75', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('76', plain,
% 1.29/1.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.29/1.50  thf('77', plain,
% 1.29/1.50      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_funct_1 @ sk_C))),
% 1.29/1.50      inference('simplify', [status(thm)], ['76'])).
% 1.29/1.50  thf('78', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('79', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('80', plain,
% 1.29/1.50      (((m1_subset_1 @ sk_C @ 
% 1.29/1.50         (k1_zfmisc_1 @ 
% 1.29/1.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['78', '79'])).
% 1.29/1.50  thf('81', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('82', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['80', '81'])).
% 1.29/1.50  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('84', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['82', '83'])).
% 1.29/1.50  thf(dt_k2_tops_2, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.50       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.29/1.50         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.29/1.50         ( m1_subset_1 @
% 1.29/1.50           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.29/1.50           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.29/1.50  thf('85', plain,
% 1.29/1.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.29/1.50         ((m1_subset_1 @ (k2_tops_2 @ X33 @ X34 @ X35) @ 
% 1.29/1.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 1.29/1.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.29/1.50          | ~ (v1_funct_2 @ X35 @ X33 @ X34)
% 1.29/1.50          | ~ (v1_funct_1 @ X35))),
% 1.29/1.50      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.29/1.50  thf('86', plain,
% 1.29/1.50      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | (m1_subset_1 @ 
% 1.29/1.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 1.29/1.50           (k1_zfmisc_1 @ 
% 1.29/1.50            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['84', '85'])).
% 1.29/1.50  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('88', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('89', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('90', plain,
% 1.29/1.50      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['88', '89'])).
% 1.29/1.50  thf('91', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('92', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['90', '91'])).
% 1.29/1.50  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('94', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['92', '93'])).
% 1.29/1.50  thf('95', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['82', '83'])).
% 1.29/1.50  thf('96', plain,
% 1.29/1.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 1.29/1.50          | ~ (v2_funct_1 @ X32)
% 1.29/1.50          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 1.29/1.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.29/1.50          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.29/1.50          | ~ (v1_funct_1 @ X32))),
% 1.29/1.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.29/1.50  thf('97', plain,
% 1.29/1.50      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C)
% 1.29/1.50        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['95', '96'])).
% 1.29/1.50  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('99', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['92', '93'])).
% 1.29/1.50  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('101', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('102', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('103', plain,
% 1.29/1.50      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50          = (k2_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['101', '102'])).
% 1.29/1.50  thf('104', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('105', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['103', '104'])).
% 1.29/1.50  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('108', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['105', '106', '107'])).
% 1.29/1.50  thf('109', plain,
% 1.29/1.50      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50          = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['97', '98', '99', '100', '108'])).
% 1.29/1.50  thf('110', plain,
% 1.29/1.50      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k2_funct_1 @ sk_C))),
% 1.29/1.50      inference('simplify', [status(thm)], ['109'])).
% 1.29/1.50  thf('111', plain,
% 1.29/1.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.50      inference('demod', [status(thm)], ['86', '87', '94', '110'])).
% 1.29/1.50  thf('112', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['17', '59'])).
% 1.29/1.50  thf('113', plain,
% 1.29/1.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['111', '112'])).
% 1.29/1.50  thf('114', plain,
% 1.29/1.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.29/1.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.29/1.50  thf('115', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['113', '114'])).
% 1.29/1.50  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(t55_funct_1, axiom,
% 1.29/1.50    (![A:$i]:
% 1.29/1.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.29/1.50       ( ( v2_funct_1 @ A ) =>
% 1.29/1.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.29/1.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.29/1.50  thf('117', plain,
% 1.29/1.50      (![X7 : $i]:
% 1.29/1.50         (~ (v2_funct_1 @ X7)
% 1.29/1.50          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 1.29/1.50          | ~ (v1_funct_1 @ X7)
% 1.29/1.50          | ~ (v1_relat_1 @ X7))),
% 1.29/1.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.29/1.50  thf('118', plain,
% 1.29/1.50      ((~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['116', '117'])).
% 1.29/1.50  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('120', plain,
% 1.29/1.50      ((~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['118', '119'])).
% 1.29/1.50  thf('121', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(cc1_relset_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.50       ( v1_relat_1 @ C ) ))).
% 1.29/1.50  thf('122', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.50         ((v1_relat_1 @ X8)
% 1.29/1.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.29/1.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.29/1.50  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.50      inference('sup-', [status(thm)], ['121', '122'])).
% 1.29/1.50  thf('124', plain,
% 1.29/1.50      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['120', '123'])).
% 1.29/1.50  thf('125', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['115', '124'])).
% 1.29/1.50  thf('126', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('127', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['17', '59'])).
% 1.29/1.50  thf('128', plain,
% 1.29/1.50      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['126', '127'])).
% 1.29/1.50  thf('129', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('130', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['128', '129'])).
% 1.29/1.50  thf('131', plain,
% 1.29/1.50      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('demod', [status(thm)],
% 1.29/1.50                ['5', '10', '60', '61', '77', '125', '130'])).
% 1.29/1.50  thf('132', plain,
% 1.29/1.50      (($false)
% 1.29/1.50         <= (~
% 1.29/1.50             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_A))))),
% 1.29/1.50      inference('simplify', [status(thm)], ['131'])).
% 1.29/1.50  thf('133', plain,
% 1.29/1.50      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['111', '112'])).
% 1.29/1.50  thf('134', plain,
% 1.29/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.29/1.50         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.29/1.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.29/1.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.50  thf('135', plain,
% 1.29/1.50      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['133', '134'])).
% 1.29/1.50  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('137', plain,
% 1.29/1.50      (![X7 : $i]:
% 1.29/1.50         (~ (v2_funct_1 @ X7)
% 1.29/1.50          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 1.29/1.50          | ~ (v1_funct_1 @ X7)
% 1.29/1.50          | ~ (v1_relat_1 @ X7))),
% 1.29/1.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.29/1.50  thf('138', plain,
% 1.29/1.50      ((~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['136', '137'])).
% 1.29/1.50  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('140', plain,
% 1.29/1.50      ((~ (v1_relat_1 @ sk_C)
% 1.29/1.50        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['138', '139'])).
% 1.29/1.50  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.50      inference('sup-', [status(thm)], ['121', '122'])).
% 1.29/1.50  thf('142', plain,
% 1.29/1.50      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['140', '141'])).
% 1.29/1.50  thf('143', plain,
% 1.29/1.50      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['135', '142'])).
% 1.29/1.50  thf('144', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['17', '59'])).
% 1.29/1.50  thf('145', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('146', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('147', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('148', plain,
% 1.29/1.50      (((m1_subset_1 @ sk_C @ 
% 1.29/1.50         (k1_zfmisc_1 @ 
% 1.29/1.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['146', '147'])).
% 1.29/1.50  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('150', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['148', '149'])).
% 1.29/1.50  thf('151', plain,
% 1.29/1.50      (((m1_subset_1 @ sk_C @ 
% 1.29/1.50         (k1_zfmisc_1 @ 
% 1.29/1.50          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['145', '150'])).
% 1.29/1.50  thf('152', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('153', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['151', '152'])).
% 1.29/1.50  thf('154', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('155', plain,
% 1.29/1.50      ((m1_subset_1 @ sk_C @ 
% 1.29/1.50        (k1_zfmisc_1 @ 
% 1.29/1.50         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.29/1.50      inference('demod', [status(thm)], ['153', '154'])).
% 1.29/1.50  thf('156', plain,
% 1.29/1.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.29/1.50         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 1.29/1.50          | ~ (v2_funct_1 @ X32)
% 1.29/1.50          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 1.29/1.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.29/1.50          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.29/1.50          | ~ (v1_funct_1 @ X32))),
% 1.29/1.50      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.29/1.50  thf('157', plain,
% 1.29/1.50      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.50        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.29/1.50        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ~ (v2_funct_1 @ sk_C)
% 1.29/1.50        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50            != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['155', '156'])).
% 1.29/1.50  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('159', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('160', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('161', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('162', plain,
% 1.29/1.50      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['160', '161'])).
% 1.29/1.50  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('164', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['162', '163'])).
% 1.29/1.50  thf('165', plain,
% 1.29/1.50      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['159', '164'])).
% 1.29/1.50  thf('166', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('167', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['165', '166'])).
% 1.29/1.50  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('169', plain,
% 1.29/1.50      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['167', '168'])).
% 1.29/1.50  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('171', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('172', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('173', plain,
% 1.29/1.50      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('174', plain,
% 1.29/1.50      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50          = (k2_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['172', '173'])).
% 1.29/1.50  thf('175', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('176', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['174', '175'])).
% 1.29/1.50  thf('177', plain,
% 1.29/1.50      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50          = (k2_struct_0 @ sk_B_2))
% 1.29/1.50        | ~ (l1_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['171', '176'])).
% 1.29/1.50  thf('178', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('179', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 1.29/1.50         = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('demod', [status(thm)], ['177', '178'])).
% 1.29/1.50  thf('180', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('181', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('182', plain,
% 1.29/1.50      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k2_relat_1 @ sk_C))),
% 1.29/1.50      inference('demod', [status(thm)], ['179', '180', '181'])).
% 1.29/1.50  thf('183', plain,
% 1.29/1.50      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50          = (k2_funct_1 @ sk_C))
% 1.29/1.50        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.29/1.50      inference('demod', [status(thm)], ['157', '158', '169', '170', '182'])).
% 1.29/1.50  thf('184', plain,
% 1.29/1.50      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.29/1.50         = (k2_funct_1 @ sk_C))),
% 1.29/1.50      inference('simplify', [status(thm)], ['183'])).
% 1.29/1.50  thf('185', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('186', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('187', plain,
% 1.29/1.50      (![X25 : $i]:
% 1.29/1.50         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.29/1.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.29/1.50  thf('188', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B_2)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('split', [status(esa)], ['1'])).
% 1.29/1.50  thf('189', plain,
% 1.29/1.50      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50           != (k2_struct_0 @ sk_B_2))
% 1.29/1.50         | ~ (l1_struct_0 @ sk_B_2)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['187', '188'])).
% 1.29/1.50  thf('190', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('191', plain,
% 1.29/1.50      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B_2)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['189', '190'])).
% 1.29/1.50  thf('192', plain,
% 1.29/1.50      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50           != (k2_struct_0 @ sk_B_2))
% 1.29/1.50         | ~ (l1_struct_0 @ sk_A)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['186', '191'])).
% 1.29/1.50  thf('193', plain, ((l1_struct_0 @ sk_A)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('194', plain,
% 1.29/1.50      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B_2)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['192', '193'])).
% 1.29/1.50  thf('195', plain,
% 1.29/1.50      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50           != (k2_struct_0 @ sk_B_2))
% 1.29/1.50         | ~ (l1_struct_0 @ sk_B_2)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['185', '194'])).
% 1.29/1.50  thf('196', plain, ((l1_struct_0 @ sk_B_2)),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('197', plain,
% 1.29/1.50      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          != (k2_struct_0 @ sk_B_2)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['195', '196'])).
% 1.29/1.50  thf('198', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('199', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('200', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.29/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('201', plain,
% 1.29/1.50      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.29/1.50          != (k2_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 1.29/1.50  thf('202', plain,
% 1.29/1.50      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['184', '201'])).
% 1.29/1.50  thf('203', plain,
% 1.29/1.50      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.29/1.50          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['144', '202'])).
% 1.29/1.50  thf('204', plain,
% 1.29/1.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.29/1.50         <= (~
% 1.29/1.50             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.29/1.50                 sk_C))
% 1.29/1.50                = (k2_struct_0 @ sk_B_2))))),
% 1.29/1.50      inference('sup-', [status(thm)], ['143', '203'])).
% 1.29/1.50  thf('205', plain,
% 1.29/1.50      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_B_2)))),
% 1.29/1.50      inference('simplify', [status(thm)], ['204'])).
% 1.29/1.50  thf('206', plain,
% 1.29/1.50      (~
% 1.29/1.50       (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_A))) | 
% 1.29/1.50       ~
% 1.29/1.50       (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_B_2)))),
% 1.29/1.50      inference('split', [status(esa)], ['1'])).
% 1.29/1.50  thf('207', plain,
% 1.29/1.50      (~
% 1.29/1.50       (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.50          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.29/1.50          = (k2_struct_0 @ sk_A)))),
% 1.29/1.50      inference('sat_resolution*', [status(thm)], ['205', '206'])).
% 1.29/1.50  thf('208', plain, ($false),
% 1.29/1.50      inference('simpl_trail', [status(thm)], ['132', '207'])).
% 1.29/1.50  
% 1.29/1.50  % SZS output end Refutation
% 1.29/1.50  
% 1.33/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
