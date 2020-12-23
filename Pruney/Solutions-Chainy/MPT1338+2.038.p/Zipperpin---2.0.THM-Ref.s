%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wlcfEvjzTJ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:53 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  229 (1304 expanded)
%              Number of leaves         :   47 ( 398 expanded)
%              Depth                    :   24
%              Number of atoms          : 2159 (31909 expanded)
%              Number of equality atoms :  162 (1765 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(rc4_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[rc4_struct_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('47',plain,(
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

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k3_tarski @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[rc4_struct_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','61'])).

thf('64',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
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

thf('66',plain,(
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

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
     != ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('72',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','61'])).

thf('74',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('77',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','59','60'])).

thf('92',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10','62','63','79','92'])).

thf('94',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('112',plain,(
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

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
      = ( k2_struct_0 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','124'])).

thf('126',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','110','126'])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','61'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('131',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
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

thf('133',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('138',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','140'])).

thf('142',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('143',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['125'])).

thf('144',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('147',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('148',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['144','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_2 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['143','160'])).

thf('162',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['142','161'])).

thf('163',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['141','162'])).

thf('164',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('166',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['164','165'])).

thf('167',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['93','166'])).

thf('168',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('169',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('170',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['137','138'])).

thf('177',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['170','177'])).

thf('179',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','178'])).

thf('180',plain,(
    $false ),
    inference(simplify,[status(thm)],['179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wlcfEvjzTJ
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:54:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.74/1.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.93  % Solved by: fo/fo7.sh
% 1.74/1.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.93  % done 629 iterations in 1.464s
% 1.74/1.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.93  % SZS output start Refutation
% 1.74/1.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.74/1.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.74/1.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.74/1.93  thf(sk_B_type, type, sk_B: $i > $i).
% 1.74/1.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.74/1.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.74/1.93  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.74/1.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.93  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.74/1.93  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.74/1.93  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.74/1.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.74/1.93  thf(sk_C_type, type, sk_C: $i).
% 1.74/1.93  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.74/1.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.74/1.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.74/1.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.93  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.74/1.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.74/1.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.74/1.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.74/1.93  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.74/1.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.74/1.93  thf(d3_struct_0, axiom,
% 1.74/1.93    (![A:$i]:
% 1.74/1.93     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.74/1.93  thf('0', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf(t62_tops_2, conjecture,
% 1.74/1.93    (![A:$i]:
% 1.74/1.93     ( ( l1_struct_0 @ A ) =>
% 1.74/1.93       ( ![B:$i]:
% 1.74/1.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.74/1.93           ( ![C:$i]:
% 1.74/1.93             ( ( ( v1_funct_1 @ C ) & 
% 1.74/1.93                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.93                 ( m1_subset_1 @
% 1.74/1.93                   C @ 
% 1.74/1.93                   ( k1_zfmisc_1 @
% 1.74/1.93                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.93               ( ( ( ( k2_relset_1 @
% 1.74/1.93                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.74/1.93                     ( k2_struct_0 @ B ) ) & 
% 1.74/1.93                   ( v2_funct_1 @ C ) ) =>
% 1.74/1.93                 ( ( ( k1_relset_1 @
% 1.74/1.93                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.74/1.93                       ( k2_tops_2 @
% 1.74/1.93                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.74/1.93                     ( k2_struct_0 @ B ) ) & 
% 1.74/1.93                   ( ( k2_relset_1 @
% 1.74/1.93                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.74/1.93                       ( k2_tops_2 @
% 1.74/1.93                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.74/1.93                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.74/1.93  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.93    (~( ![A:$i]:
% 1.74/1.93        ( ( l1_struct_0 @ A ) =>
% 1.74/1.93          ( ![B:$i]:
% 1.74/1.93            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.74/1.93              ( ![C:$i]:
% 1.74/1.93                ( ( ( v1_funct_1 @ C ) & 
% 1.74/1.93                    ( v1_funct_2 @
% 1.74/1.93                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.93                    ( m1_subset_1 @
% 1.74/1.93                      C @ 
% 1.74/1.93                      ( k1_zfmisc_1 @
% 1.74/1.93                        ( k2_zfmisc_1 @
% 1.74/1.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.93                  ( ( ( ( k2_relset_1 @
% 1.74/1.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.74/1.93                        ( k2_struct_0 @ B ) ) & 
% 1.74/1.93                      ( v2_funct_1 @ C ) ) =>
% 1.74/1.93                    ( ( ( k1_relset_1 @
% 1.74/1.93                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.74/1.93                          ( k2_tops_2 @
% 1.74/1.93                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.74/1.93                        ( k2_struct_0 @ B ) ) & 
% 1.74/1.93                      ( ( k2_relset_1 @
% 1.74/1.93                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.74/1.93                          ( k2_tops_2 @
% 1.74/1.93                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.74/1.93                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.74/1.93    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.74/1.93  thf('1', plain,
% 1.74/1.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_B_2))
% 1.74/1.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93            != (k2_struct_0 @ sk_A)))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('2', plain,
% 1.74/1.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_A)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_A))))),
% 1.74/1.93      inference('split', [status(esa)], ['1'])).
% 1.74/1.93  thf('3', plain,
% 1.74/1.93      (((((k2_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93           != (k2_struct_0 @ sk_A))
% 1.74/1.93         | ~ (l1_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_A))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['0', '2'])).
% 1.74/1.93  thf('4', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('5', plain,
% 1.74/1.93      ((((k2_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_A)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_A))))),
% 1.74/1.93      inference('demod', [status(thm)], ['3', '4'])).
% 1.74/1.93  thf('6', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf(redefinition_k2_relset_1, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.93       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.74/1.93  thf('7', plain,
% 1.74/1.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.74/1.93         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.74/1.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.74/1.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.74/1.93  thf('8', plain,
% 1.74/1.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k2_relat_1 @ sk_C))),
% 1.74/1.93      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.93  thf('9', plain,
% 1.74/1.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('10', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('11', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('12', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf(d1_funct_2, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.74/1.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.74/1.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.74/1.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.74/1.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.74/1.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.74/1.93  thf(zf_stmt_1, axiom,
% 1.74/1.93    (![C:$i,B:$i,A:$i]:
% 1.74/1.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.74/1.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.74/1.93  thf('13', plain,
% 1.74/1.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.74/1.93         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 1.74/1.93          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 1.74/1.93          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.74/1.93  thf('14', plain,
% 1.74/1.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 1.74/1.93        | ((u1_struct_0 @ sk_A)
% 1.74/1.93            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93               sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['12', '13'])).
% 1.74/1.93  thf('15', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf(redefinition_k1_relset_1, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.74/1.93  thf('16', plain,
% 1.74/1.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.74/1.93         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 1.74/1.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.74/1.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.74/1.93  thf('17', plain,
% 1.74/1.93      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('sup-', [status(thm)], ['15', '16'])).
% 1.74/1.93  thf('18', plain,
% 1.74/1.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 1.74/1.93        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['14', '17'])).
% 1.74/1.93  thf('19', plain,
% 1.74/1.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_A)
% 1.74/1.93        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['11', '18'])).
% 1.74/1.93  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('21', plain,
% 1.74/1.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.74/1.93        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['19', '20'])).
% 1.74/1.93  thf('22', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('23', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('24', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('25', plain,
% 1.74/1.93      (((m1_subset_1 @ sk_C @ 
% 1.74/1.93         (k1_zfmisc_1 @ 
% 1.74/1.93          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_A))),
% 1.74/1.93      inference('sup+', [status(thm)], ['23', '24'])).
% 1.74/1.93  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('27', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['25', '26'])).
% 1.74/1.93  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.74/1.93  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.74/1.93  thf(zf_stmt_4, axiom,
% 1.74/1.93    (![B:$i,A:$i]:
% 1.74/1.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.74/1.93       ( zip_tseitin_0 @ B @ A ) ))).
% 1.74/1.93  thf(zf_stmt_5, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.74/1.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.74/1.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.74/1.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.74/1.93  thf('28', plain,
% 1.74/1.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.74/1.93         (~ (zip_tseitin_0 @ X20 @ X21)
% 1.74/1.93          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 1.74/1.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.74/1.93  thf('29', plain,
% 1.74/1.93      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.74/1.93        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['27', '28'])).
% 1.74/1.93  thf('30', plain,
% 1.74/1.93      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_B_2)
% 1.74/1.93        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['22', '29'])).
% 1.74/1.93  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('33', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf(rc4_struct_0, axiom,
% 1.74/1.93    (![A:$i]:
% 1.74/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.74/1.93       ( ?[B:$i]:
% 1.74/1.93         ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.74/1.93           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.74/1.93  thf('34', plain,
% 1.74/1.93      (![X24 : $i]:
% 1.74/1.93         ((m1_subset_1 @ (sk_B @ X24) @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.74/1.93          | ~ (l1_struct_0 @ X24)
% 1.74/1.93          | (v2_struct_0 @ X24))),
% 1.74/1.93      inference('cnf', [status(esa)], [rc4_struct_0])).
% 1.74/1.93  thf('35', plain,
% 1.74/1.93      (![X0 : $i]:
% 1.74/1.93         ((m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.74/1.93          | ~ (l1_struct_0 @ X0)
% 1.74/1.93          | (v2_struct_0 @ X0)
% 1.74/1.93          | ~ (l1_struct_0 @ X0))),
% 1.74/1.93      inference('sup+', [status(thm)], ['33', '34'])).
% 1.74/1.93  thf('36', plain,
% 1.74/1.93      (![X0 : $i]:
% 1.74/1.93         ((v2_struct_0 @ X0)
% 1.74/1.93          | ~ (l1_struct_0 @ X0)
% 1.74/1.93          | (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.74/1.93      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.93  thf('37', plain,
% 1.74/1.93      (((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_B_2)
% 1.74/1.93        | (v2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['32', '36'])).
% 1.74/1.93  thf('38', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('39', plain,
% 1.74/1.93      (((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 1.74/1.93        | (v2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('demod', [status(thm)], ['37', '38'])).
% 1.74/1.93  thf('40', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('41', plain,
% 1.74/1.93      ((m1_subset_1 @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 1.74/1.93      inference('clc', [status(thm)], ['39', '40'])).
% 1.74/1.93  thf(d2_subset_1, axiom,
% 1.74/1.93    (![A:$i,B:$i]:
% 1.74/1.93     ( ( ( v1_xboole_0 @ A ) =>
% 1.74/1.93         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.74/1.93       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.74/1.93         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.74/1.93  thf('42', plain,
% 1.74/1.93      (![X1 : $i, X2 : $i]:
% 1.74/1.93         (~ (m1_subset_1 @ X1 @ X2)
% 1.74/1.93          | (r2_hidden @ X1 @ X2)
% 1.74/1.93          | (v1_xboole_0 @ X2))),
% 1.74/1.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.74/1.93  thf('43', plain,
% 1.74/1.93      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 1.74/1.93        | (r2_hidden @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['41', '42'])).
% 1.74/1.93  thf(fc1_subset_1, axiom,
% 1.74/1.93    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.74/1.93  thf('44', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 1.74/1.93      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.74/1.93  thf('45', plain,
% 1.74/1.93      ((r2_hidden @ (sk_B @ sk_B_2) @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 1.74/1.93      inference('clc', [status(thm)], ['43', '44'])).
% 1.74/1.93  thf('46', plain,
% 1.74/1.93      (![X15 : $i, X16 : $i]:
% 1.74/1.93         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.74/1.93  thf(t99_zfmisc_1, axiom,
% 1.74/1.93    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.74/1.93  thf('47', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 1.74/1.93      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.74/1.93  thf(t91_orders_1, axiom,
% 1.74/1.93    (![A:$i]:
% 1.74/1.93     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 1.74/1.93            ( ![B:$i]:
% 1.74/1.93              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 1.74/1.93       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 1.74/1.93            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.74/1.93  thf('48', plain,
% 1.74/1.93      (![X25 : $i, X26 : $i]:
% 1.74/1.93         (((X25) = (k1_xboole_0))
% 1.74/1.93          | ~ (r2_hidden @ X25 @ X26)
% 1.74/1.93          | ((k3_tarski @ X26) != (k1_xboole_0)))),
% 1.74/1.93      inference('cnf', [status(esa)], [t91_orders_1])).
% 1.74/1.93  thf('49', plain,
% 1.74/1.93      (![X0 : $i, X1 : $i]:
% 1.74/1.93         (((X0) != (k1_xboole_0))
% 1.74/1.93          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 1.74/1.93          | ((X1) = (k1_xboole_0)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['47', '48'])).
% 1.74/1.93  thf('50', plain,
% 1.74/1.93      (![X1 : $i]:
% 1.74/1.93         (((X1) = (k1_xboole_0))
% 1.74/1.93          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.74/1.93      inference('simplify', [status(thm)], ['49'])).
% 1.74/1.93  thf('51', plain,
% 1.74/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.93         (~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 1.74/1.93          | (zip_tseitin_0 @ X0 @ X2)
% 1.74/1.93          | ((X1) = (k1_xboole_0)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['46', '50'])).
% 1.74/1.93  thf('52', plain,
% 1.74/1.93      (![X0 : $i]:
% 1.74/1.93         (((sk_B @ sk_B_2) = (k1_xboole_0))
% 1.74/1.93          | (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 1.74/1.93      inference('sup-', [status(thm)], ['45', '51'])).
% 1.74/1.93  thf('53', plain,
% 1.74/1.93      (![X24 : $i]:
% 1.74/1.93         (~ (v1_xboole_0 @ (sk_B @ X24))
% 1.74/1.93          | ~ (l1_struct_0 @ X24)
% 1.74/1.93          | (v2_struct_0 @ X24))),
% 1.74/1.93      inference('cnf', [status(esa)], [rc4_struct_0])).
% 1.74/1.93  thf('54', plain,
% 1.74/1.93      (![X0 : $i]:
% 1.74/1.93         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.74/1.93          | (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 1.74/1.93          | (v2_struct_0 @ sk_B_2)
% 1.74/1.93          | ~ (l1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup-', [status(thm)], ['52', '53'])).
% 1.74/1.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.74/1.93  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.74/1.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.74/1.93  thf('56', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('57', plain,
% 1.74/1.93      (![X0 : $i]:
% 1.74/1.93         ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0) | (v2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.74/1.93  thf('58', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('59', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)),
% 1.74/1.93      inference('clc', [status(thm)], ['57', '58'])).
% 1.74/1.93  thf('60', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('61', plain,
% 1.74/1.93      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))),
% 1.74/1.93      inference('demod', [status(thm)], ['30', '31', '59', '60'])).
% 1.74/1.93  thf('62', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['21', '61'])).
% 1.74/1.93  thf('63', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['21', '61'])).
% 1.74/1.93  thf('64', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('65', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf(d4_tops_2, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.74/1.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.74/1.93         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.74/1.93  thf('66', plain,
% 1.74/1.93      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.93         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 1.74/1.93          | ~ (v2_funct_1 @ X30)
% 1.74/1.93          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 1.74/1.93          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.74/1.93          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 1.74/1.93          | ~ (v1_funct_1 @ X30))),
% 1.74/1.93      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.74/1.93  thf('67', plain,
% 1.74/1.93      ((~ (v1_funct_1 @ sk_C)
% 1.74/1.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 1.74/1.93        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93            = (k2_funct_1 @ sk_C))
% 1.74/1.93        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93            != (u1_struct_0 @ sk_B_2)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['65', '66'])).
% 1.74/1.93  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('69', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('71', plain,
% 1.74/1.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k2_relat_1 @ sk_C))),
% 1.74/1.93      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.93  thf('72', plain,
% 1.74/1.93      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93          = (k2_funct_1 @ sk_C))
% 1.74/1.93        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B_2)))),
% 1.74/1.93      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 1.74/1.93  thf('73', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['21', '61'])).
% 1.74/1.93  thf('74', plain,
% 1.74/1.93      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93          = (k2_funct_1 @ sk_C))
% 1.74/1.93        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B_2)))),
% 1.74/1.93      inference('demod', [status(thm)], ['72', '73'])).
% 1.74/1.93  thf('75', plain,
% 1.74/1.93      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B_2))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_B_2)
% 1.74/1.93        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93            = (k2_funct_1 @ sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['64', '74'])).
% 1.74/1.93  thf('76', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('77', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('78', plain,
% 1.74/1.93      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.74/1.93        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93            = (k2_funct_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.74/1.93  thf('79', plain,
% 1.74/1.93      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k2_funct_1 @ sk_C))),
% 1.74/1.93      inference('simplify', [status(thm)], ['78'])).
% 1.74/1.93  thf('80', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('81', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('82', plain,
% 1.74/1.93      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_A))),
% 1.74/1.93      inference('sup+', [status(thm)], ['80', '81'])).
% 1.74/1.93  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('84', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('demod', [status(thm)], ['82', '83'])).
% 1.74/1.93  thf('85', plain,
% 1.74/1.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.74/1.93         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 1.74/1.93          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 1.74/1.93          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.74/1.93  thf('86', plain,
% 1.74/1.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.74/1.93        | ((k2_struct_0 @ sk_A)
% 1.74/1.93            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93               sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['84', '85'])).
% 1.74/1.93  thf('87', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['25', '26'])).
% 1.74/1.93  thf('88', plain,
% 1.74/1.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.74/1.93         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 1.74/1.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.74/1.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.74/1.93  thf('89', plain,
% 1.74/1.93      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('sup-', [status(thm)], ['87', '88'])).
% 1.74/1.93  thf('90', plain,
% 1.74/1.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))
% 1.74/1.93        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['86', '89'])).
% 1.74/1.93  thf('91', plain,
% 1.74/1.93      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A))),
% 1.74/1.93      inference('demod', [status(thm)], ['30', '31', '59', '60'])).
% 1.74/1.93  thf('92', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['90', '91'])).
% 1.74/1.93  thf('93', plain,
% 1.74/1.93      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_A))))),
% 1.74/1.93      inference('demod', [status(thm)], ['5', '10', '62', '63', '79', '92'])).
% 1.74/1.93  thf('94', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('95', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('96', plain,
% 1.74/1.93      (((m1_subset_1 @ sk_C @ 
% 1.74/1.93         (k1_zfmisc_1 @ 
% 1.74/1.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['94', '95'])).
% 1.74/1.93  thf('97', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('98', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['96', '97'])).
% 1.74/1.93  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('100', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.74/1.93      inference('demod', [status(thm)], ['98', '99'])).
% 1.74/1.93  thf(dt_k2_tops_2, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.74/1.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.93       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.74/1.93         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.74/1.93         ( m1_subset_1 @
% 1.74/1.93           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.74/1.93           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.74/1.93  thf('101', plain,
% 1.74/1.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.74/1.93         ((m1_subset_1 @ (k2_tops_2 @ X31 @ X32 @ X33) @ 
% 1.74/1.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.74/1.93          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.74/1.93          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.74/1.93          | ~ (v1_funct_1 @ X33))),
% 1.74/1.93      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.74/1.93  thf('102', plain,
% 1.74/1.93      ((~ (v1_funct_1 @ sk_C)
% 1.74/1.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.74/1.93        | (m1_subset_1 @ 
% 1.74/1.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 1.74/1.93           (k1_zfmisc_1 @ 
% 1.74/1.93            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['100', '101'])).
% 1.74/1.93  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('104', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('105', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('106', plain,
% 1.74/1.93      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['104', '105'])).
% 1.74/1.93  thf('107', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('108', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('demod', [status(thm)], ['106', '107'])).
% 1.74/1.93  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('110', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['108', '109'])).
% 1.74/1.93  thf('111', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.74/1.93      inference('demod', [status(thm)], ['98', '99'])).
% 1.74/1.93  thf('112', plain,
% 1.74/1.93      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.93         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 1.74/1.93          | ~ (v2_funct_1 @ X30)
% 1.74/1.93          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 1.74/1.93          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.74/1.93          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 1.74/1.93          | ~ (v1_funct_1 @ X30))),
% 1.74/1.93      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.74/1.93  thf('113', plain,
% 1.74/1.93      ((~ (v1_funct_1 @ sk_C)
% 1.74/1.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.74/1.93        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.74/1.93            = (k2_funct_1 @ sk_C))
% 1.74/1.93        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.74/1.93            != (k2_relat_1 @ sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['111', '112'])).
% 1.74/1.93  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('115', plain,
% 1.74/1.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['108', '109'])).
% 1.74/1.93  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('117', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('118', plain,
% 1.74/1.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('119', plain,
% 1.74/1.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93          = (k2_struct_0 @ sk_B_2))
% 1.74/1.93        | ~ (l1_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['117', '118'])).
% 1.74/1.93  thf('120', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('121', plain,
% 1.74/1.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C)
% 1.74/1.93         = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('demod', [status(thm)], ['119', '120'])).
% 1.74/1.93  thf('122', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('124', plain,
% 1.74/1.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.74/1.93         = (k2_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['121', '122', '123'])).
% 1.74/1.93  thf('125', plain,
% 1.74/1.93      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.74/1.93          = (k2_funct_1 @ sk_C))
% 1.74/1.93        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['113', '114', '115', '116', '124'])).
% 1.74/1.93  thf('126', plain,
% 1.74/1.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.74/1.93         = (k2_funct_1 @ sk_C))),
% 1.74/1.93      inference('simplify', [status(thm)], ['125'])).
% 1.74/1.93  thf('127', plain,
% 1.74/1.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.74/1.93      inference('demod', [status(thm)], ['102', '103', '110', '126'])).
% 1.74/1.93  thf('128', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['21', '61'])).
% 1.74/1.93  thf('129', plain,
% 1.74/1.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.74/1.93      inference('demod', [status(thm)], ['127', '128'])).
% 1.74/1.93  thf('130', plain,
% 1.74/1.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.74/1.93         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 1.74/1.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.74/1.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.74/1.93  thf('131', plain,
% 1.74/1.93      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['129', '130'])).
% 1.74/1.93  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf(t55_funct_1, axiom,
% 1.74/1.93    (![A:$i]:
% 1.74/1.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.93       ( ( v2_funct_1 @ A ) =>
% 1.74/1.93         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.74/1.93           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.74/1.93  thf('133', plain,
% 1.74/1.93      (![X5 : $i]:
% 1.74/1.93         (~ (v2_funct_1 @ X5)
% 1.74/1.93          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 1.74/1.93          | ~ (v1_funct_1 @ X5)
% 1.74/1.93          | ~ (v1_relat_1 @ X5))),
% 1.74/1.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.93  thf('134', plain,
% 1.74/1.93      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.93        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.93        | ~ (v2_funct_1 @ sk_C))),
% 1.74/1.93      inference('sup-', [status(thm)], ['132', '133'])).
% 1.74/1.93  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('136', plain,
% 1.74/1.93      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.93        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.93      inference('demod', [status(thm)], ['134', '135'])).
% 1.74/1.93  thf('137', plain,
% 1.74/1.93      ((m1_subset_1 @ sk_C @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf(cc1_relset_1, axiom,
% 1.74/1.93    (![A:$i,B:$i,C:$i]:
% 1.74/1.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.93       ( v1_relat_1 @ C ) ))).
% 1.74/1.93  thf('138', plain,
% 1.74/1.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.74/1.93         ((v1_relat_1 @ X6)
% 1.74/1.93          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.74/1.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.93  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.93      inference('sup-', [status(thm)], ['137', '138'])).
% 1.74/1.93  thf('140', plain,
% 1.74/1.93      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['136', '139'])).
% 1.74/1.93  thf('141', plain,
% 1.74/1.93      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['131', '140'])).
% 1.74/1.93  thf('142', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['90', '91'])).
% 1.74/1.93  thf('143', plain,
% 1.74/1.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.74/1.93         = (k2_funct_1 @ sk_C))),
% 1.74/1.93      inference('simplify', [status(thm)], ['125'])).
% 1.74/1.93  thf('144', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('145', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('146', plain,
% 1.74/1.93      (![X23 : $i]:
% 1.74/1.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.74/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.93  thf('147', plain,
% 1.74/1.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('split', [status(esa)], ['1'])).
% 1.74/1.93  thf('148', plain,
% 1.74/1.93      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93           != (k2_struct_0 @ sk_B_2))
% 1.74/1.93         | ~ (l1_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['146', '147'])).
% 1.74/1.93  thf('149', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('150', plain,
% 1.74/1.93      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['148', '149'])).
% 1.74/1.93  thf('151', plain,
% 1.74/1.93      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93           != (k2_struct_0 @ sk_B_2))
% 1.74/1.93         | ~ (l1_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['145', '150'])).
% 1.74/1.93  thf('152', plain, ((l1_struct_0 @ sk_B_2)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('153', plain,
% 1.74/1.93      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['151', '152'])).
% 1.74/1.93  thf('154', plain,
% 1.74/1.93      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A) @ 
% 1.74/1.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93           != (k2_struct_0 @ sk_B_2))
% 1.74/1.93         | ~ (l1_struct_0 @ sk_A)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['144', '153'])).
% 1.74/1.93  thf('155', plain, ((l1_struct_0 @ sk_A)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('156', plain,
% 1.74/1.93      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_2) @ (k2_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          != (k2_struct_0 @ sk_B_2)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['154', '155'])).
% 1.74/1.93  thf('157', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('158', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B_2))),
% 1.74/1.93      inference('sup+', [status(thm)], ['8', '9'])).
% 1.74/1.93  thf('160', plain,
% 1.74/1.93      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.74/1.93          != (k2_relat_1 @ sk_C)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 1.74/1.93  thf('161', plain,
% 1.74/1.93      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['143', '160'])).
% 1.74/1.93  thf('162', plain,
% 1.74/1.93      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['142', '161'])).
% 1.74/1.93  thf('163', plain,
% 1.74/1.93      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.74/1.93         <= (~
% 1.74/1.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.93                 sk_C))
% 1.74/1.93                = (k2_struct_0 @ sk_B_2))))),
% 1.74/1.93      inference('sup-', [status(thm)], ['141', '162'])).
% 1.74/1.93  thf('164', plain,
% 1.74/1.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          = (k2_struct_0 @ sk_B_2)))),
% 1.74/1.93      inference('simplify', [status(thm)], ['163'])).
% 1.74/1.93  thf('165', plain,
% 1.74/1.93      (~
% 1.74/1.93       (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          = (k2_struct_0 @ sk_A))) | 
% 1.74/1.93       ~
% 1.74/1.93       (((k1_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          = (k2_struct_0 @ sk_B_2)))),
% 1.74/1.93      inference('split', [status(esa)], ['1'])).
% 1.74/1.93  thf('166', plain,
% 1.74/1.93      (~
% 1.74/1.93       (((k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C))
% 1.74/1.93          = (k2_struct_0 @ sk_A)))),
% 1.74/1.93      inference('sat_resolution*', [status(thm)], ['164', '165'])).
% 1.74/1.93  thf('167', plain,
% 1.74/1.93      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('simpl_trail', [status(thm)], ['93', '166'])).
% 1.74/1.93  thf('168', plain,
% 1.74/1.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.74/1.93        (k1_zfmisc_1 @ 
% 1.74/1.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.74/1.93      inference('demod', [status(thm)], ['127', '128'])).
% 1.74/1.93  thf('169', plain,
% 1.74/1.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.74/1.93         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.74/1.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.74/1.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.74/1.93  thf('170', plain,
% 1.74/1.93      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.93      inference('sup-', [status(thm)], ['168', '169'])).
% 1.74/1.93  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('172', plain,
% 1.74/1.93      (![X5 : $i]:
% 1.74/1.93         (~ (v2_funct_1 @ X5)
% 1.74/1.93          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 1.74/1.93          | ~ (v1_funct_1 @ X5)
% 1.74/1.93          | ~ (v1_relat_1 @ X5))),
% 1.74/1.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.93  thf('173', plain,
% 1.74/1.93      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.93        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.93        | ~ (v2_funct_1 @ sk_C))),
% 1.74/1.93      inference('sup-', [status(thm)], ['171', '172'])).
% 1.74/1.93  thf('174', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.93  thf('175', plain,
% 1.74/1.93      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.93        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.93      inference('demod', [status(thm)], ['173', '174'])).
% 1.74/1.93  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.93      inference('sup-', [status(thm)], ['137', '138'])).
% 1.74/1.93  thf('177', plain,
% 1.74/1.93      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.93      inference('demod', [status(thm)], ['175', '176'])).
% 1.74/1.93  thf('178', plain,
% 1.74/1.93      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.74/1.93         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['170', '177'])).
% 1.74/1.93  thf('179', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.74/1.93      inference('demod', [status(thm)], ['167', '178'])).
% 1.74/1.93  thf('180', plain, ($false), inference('simplify', [status(thm)], ['179'])).
% 1.74/1.93  
% 1.74/1.93  % SZS output end Refutation
% 1.74/1.93  
% 1.74/1.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
