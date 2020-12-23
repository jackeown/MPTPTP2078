%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1wmRSsNnTP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:52 EST 2020

% Result     : Theorem 42.59s
% Output     : Refutation 42.59s
% Verified   : 
% Statistics : Number of formulae       :  249 (2073 expanded)
%              Number of leaves         :   61 ( 624 expanded)
%              Depth                    :   28
%              Number of atoms          : 2147 (55772 expanded)
%              Number of equality atoms :  207 (3277 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
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

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( v1_xboole_0 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('10',plain,(
    ! [X14: $i] :
      ( v1_xboole_0 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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

thf('16',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
    | ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 != k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_3 ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('47',plain,
    ( ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B_3 ) @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['6','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('58',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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

thf('62',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k2_relset_1 @ X48 @ X47 @ X49 )
       != X47 )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_tops_2 @ X48 @ X47 @ X49 )
        = ( k2_funct_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('68',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('71',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('76',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_funct_1 @ X39 )
      | ( ( k2_relset_1 @ X41 @ X40 @ X39 )
       != X40 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('81',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('85',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('89',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','73','89'])).

thf('91',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('93',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('96',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('97',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('99',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ( ( ( k2_relat_1 @ sk_C_1 )
       != ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('103',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['101','104','105','106'])).

thf('108',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('110',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['90','110'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('114',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','116'])).

thf('118',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['5','118'])).

thf('120',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('123',plain,
    ( ( ( k2_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('125',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('131',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['117'])).

thf('134',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['119','134'])).

thf('136',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(rc20_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('137',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('140',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('143',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X6 ) )
      = X6 ) ),
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

thf('144',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( r2_hidden @ X44 @ X45 )
      | ( ( k3_tarski @ X45 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_B_1 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_B_3 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['135','148'])).

thf('150',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('151',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['119','134'])).

thf('153',plain,
    ( ( ( sk_B_1 @ sk_B_3 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_3 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( sk_B_1 @ sk_B_3 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['153','154'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('156',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('157',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
       != ( k1_subset_1 @ X16 ) )
      | ( r1_tarski @ X17 @ ( k3_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('158',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ ( k1_subset_1 @ X16 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ( r1_tarski @ ( k1_subset_1 @ X16 ) @ ( k3_subset_1 @ X16 @ ( k1_subset_1 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('160',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('162',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('165',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('166',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('167',plain,(
    ! [X15: $i] :
      ( X15
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X16: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X16 ) @ X16 ) ),
    inference(demod,[status(thm)],['158','163','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['156','169'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('171',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('172',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','172'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('174',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('175',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('176',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('177',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,
    ( ( sk_B_1 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['155','179'])).

thf('181',plain,(
    ! [X43: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('182',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_3 )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('184',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_struct_0 @ sk_B_3 ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    $false ),
    inference(demod,[status(thm)],['0','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1wmRSsNnTP
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 42.59/42.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 42.59/42.77  % Solved by: fo/fo7.sh
% 42.59/42.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.59/42.77  % done 19618 iterations in 42.314s
% 42.59/42.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 42.59/42.77  % SZS output start Refutation
% 42.59/42.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.59/42.77  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 42.59/42.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 42.59/42.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 42.59/42.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 42.59/42.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 42.59/42.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 42.59/42.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 42.59/42.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 42.59/42.77  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 42.59/42.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 42.59/42.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 42.59/42.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 42.59/42.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 42.59/42.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 42.59/42.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 42.59/42.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 42.59/42.77  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 42.59/42.77  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 42.59/42.77  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 42.59/42.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 42.59/42.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 42.59/42.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 42.59/42.77  thf(sk_A_type, type, sk_A: $i).
% 42.59/42.77  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 42.59/42.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 42.59/42.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 42.59/42.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 42.59/42.77  thf(sk_B_3_type, type, sk_B_3: $i).
% 42.59/42.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 42.59/42.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 42.59/42.77  thf(sk_B_type, type, sk_B: $i > $i).
% 42.59/42.77  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 42.59/42.77  thf(t62_tops_2, conjecture,
% 42.59/42.77    (![A:$i]:
% 42.59/42.77     ( ( l1_struct_0 @ A ) =>
% 42.59/42.77       ( ![B:$i]:
% 42.59/42.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 42.59/42.77           ( ![C:$i]:
% 42.59/42.77             ( ( ( v1_funct_1 @ C ) & 
% 42.59/42.77                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 42.59/42.77                 ( m1_subset_1 @
% 42.59/42.77                   C @ 
% 42.59/42.77                   ( k1_zfmisc_1 @
% 42.59/42.77                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 42.59/42.77               ( ( ( ( k2_relset_1 @
% 42.59/42.77                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 42.59/42.77                     ( k2_struct_0 @ B ) ) & 
% 42.59/42.77                   ( v2_funct_1 @ C ) ) =>
% 42.59/42.77                 ( ( ( k1_relset_1 @
% 42.59/42.77                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 42.59/42.77                       ( k2_tops_2 @
% 42.59/42.77                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 42.59/42.77                     ( k2_struct_0 @ B ) ) & 
% 42.59/42.77                   ( ( k2_relset_1 @
% 42.59/42.77                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 42.59/42.77                       ( k2_tops_2 @
% 42.59/42.77                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 42.59/42.77                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 42.59/42.77  thf(zf_stmt_0, negated_conjecture,
% 42.59/42.77    (~( ![A:$i]:
% 42.59/42.77        ( ( l1_struct_0 @ A ) =>
% 42.59/42.77          ( ![B:$i]:
% 42.59/42.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 42.59/42.77              ( ![C:$i]:
% 42.59/42.77                ( ( ( v1_funct_1 @ C ) & 
% 42.59/42.77                    ( v1_funct_2 @
% 42.59/42.77                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 42.59/42.77                    ( m1_subset_1 @
% 42.59/42.77                      C @ 
% 42.59/42.77                      ( k1_zfmisc_1 @
% 42.59/42.77                        ( k2_zfmisc_1 @
% 42.59/42.77                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 42.59/42.77                  ( ( ( ( k2_relset_1 @
% 42.59/42.77                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 42.59/42.77                        ( k2_struct_0 @ B ) ) & 
% 42.59/42.77                      ( v2_funct_1 @ C ) ) =>
% 42.59/42.77                    ( ( ( k1_relset_1 @
% 42.59/42.77                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 42.59/42.77                          ( k2_tops_2 @
% 42.59/42.77                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 42.59/42.77                        ( k2_struct_0 @ B ) ) & 
% 42.59/42.77                      ( ( k2_relset_1 @
% 42.59/42.77                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 42.59/42.77                          ( k2_tops_2 @
% 42.59/42.77                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 42.59/42.77                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 42.59/42.77    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 42.59/42.77  thf('0', plain, (~ (v2_struct_0 @ sk_B_3)),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.77  thf('1', plain,
% 42.59/42.77      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.77        (k1_zfmisc_1 @ 
% 42.59/42.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.77  thf(redefinition_k2_relset_1, axiom,
% 42.59/42.77    (![A:$i,B:$i,C:$i]:
% 42.59/42.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.59/42.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 42.59/42.77  thf('2', plain,
% 42.59/42.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 42.59/42.77         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 42.59/42.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 42.59/42.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 42.59/42.77  thf('3', plain,
% 42.59/42.77      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.77         = (k2_relat_1 @ sk_C_1))),
% 42.59/42.77      inference('sup-', [status(thm)], ['1', '2'])).
% 42.59/42.77  thf('4', plain,
% 42.59/42.77      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.77         = (k2_struct_0 @ sk_B_3))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.77  thf('5', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.77      inference('sup+', [status(thm)], ['3', '4'])).
% 42.59/42.77  thf(d3_struct_0, axiom,
% 42.59/42.77    (![A:$i]:
% 42.59/42.77     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 42.59/42.77  thf('6', plain,
% 42.59/42.77      (![X42 : $i]:
% 42.59/42.77         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.77  thf('7', plain,
% 42.59/42.77      (![X42 : $i]:
% 42.59/42.77         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.77  thf(d1_funct_2, axiom,
% 42.59/42.77    (![A:$i,B:$i,C:$i]:
% 42.59/42.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.59/42.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 42.59/42.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 42.59/42.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 42.59/42.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 42.59/42.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 42.59/42.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 42.59/42.77  thf(zf_stmt_1, axiom,
% 42.59/42.77    (![B:$i,A:$i]:
% 42.59/42.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 42.59/42.77       ( zip_tseitin_0 @ B @ A ) ))).
% 42.59/42.77  thf('8', plain,
% 42.59/42.77      (![X31 : $i, X32 : $i]:
% 42.59/42.77         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 42.59/42.77  thf(rc2_subset_1, axiom,
% 42.59/42.77    (![A:$i]:
% 42.59/42.77     ( ?[B:$i]:
% 42.59/42.77       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 42.59/42.77  thf('9', plain, (![X14 : $i]: (v1_xboole_0 @ (sk_B @ X14))),
% 42.59/42.77      inference('cnf', [status(esa)], [rc2_subset_1])).
% 42.59/42.77  thf('10', plain, (![X14 : $i]: (v1_xboole_0 @ (sk_B @ X14))),
% 42.59/42.77      inference('cnf', [status(esa)], [rc2_subset_1])).
% 42.59/42.77  thf(l13_xboole_0, axiom,
% 42.59/42.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 42.59/42.77  thf('11', plain,
% 42.59/42.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 42.59/42.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 42.59/42.77  thf('12', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 42.59/42.77      inference('sup-', [status(thm)], ['10', '11'])).
% 42.59/42.77  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 42.59/42.77      inference('demod', [status(thm)], ['9', '12'])).
% 42.59/42.77  thf('14', plain,
% 42.59/42.77      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 42.59/42.77      inference('sup+', [status(thm)], ['8', '13'])).
% 42.59/42.77  thf('15', plain,
% 42.59/42.77      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.77        (k1_zfmisc_1 @ 
% 42.59/42.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 42.59/42.77  thf(zf_stmt_3, axiom,
% 42.59/42.77    (![C:$i,B:$i,A:$i]:
% 42.59/42.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 42.59/42.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 42.59/42.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 42.59/42.77  thf(zf_stmt_5, axiom,
% 42.59/42.77    (![A:$i,B:$i,C:$i]:
% 42.59/42.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.59/42.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 42.59/42.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 42.59/42.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 42.59/42.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 42.59/42.77  thf('16', plain,
% 42.59/42.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 42.59/42.77         (~ (zip_tseitin_0 @ X36 @ X37)
% 42.59/42.77          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 42.59/42.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 42.59/42.77  thf('17', plain,
% 42.59/42.77      (((zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 42.59/42.77        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['15', '16'])).
% 42.59/42.77  thf('18', plain,
% 42.59/42.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 42.59/42.77        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.77           (u1_struct_0 @ sk_A)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['14', '17'])).
% 42.59/42.77  thf('19', plain,
% 42.59/42.77      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.77  thf('20', plain,
% 42.59/42.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 42.59/42.77         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 42.59/42.77          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 42.59/42.77          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 42.59/42.77  thf('21', plain,
% 42.59/42.77      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.77           (u1_struct_0 @ sk_A))
% 42.59/42.77        | ((u1_struct_0 @ sk_A)
% 42.59/42.77            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.77               sk_C_1)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['19', '20'])).
% 42.59/42.77  thf('22', plain,
% 42.59/42.77      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.77        (k1_zfmisc_1 @ 
% 42.59/42.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.77  thf(redefinition_k1_relset_1, axiom,
% 42.59/42.77    (![A:$i,B:$i,C:$i]:
% 42.59/42.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.59/42.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 42.59/42.77  thf('23', plain,
% 42.59/42.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.59/42.77         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 42.59/42.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 42.59/42.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 42.59/42.77  thf('24', plain,
% 42.59/42.77      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.77         = (k1_relat_1 @ sk_C_1))),
% 42.59/42.77      inference('sup-', [status(thm)], ['22', '23'])).
% 42.59/42.77  thf('25', plain,
% 42.59/42.77      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.77           (u1_struct_0 @ sk_A))
% 42.59/42.77        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.77      inference('demod', [status(thm)], ['21', '24'])).
% 42.59/42.77  thf('26', plain,
% 42.59/42.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 42.59/42.77        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['18', '25'])).
% 42.59/42.77  thf('27', plain,
% 42.59/42.77      (![X31 : $i, X32 : $i]:
% 42.59/42.77         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 42.59/42.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 42.59/42.77  thf('28', plain,
% 42.59/42.77      (((zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 42.59/42.77        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['15', '16'])).
% 42.59/42.77  thf('29', plain,
% 42.59/42.77      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 42.59/42.77        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.77           (u1_struct_0 @ sk_A)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['27', '28'])).
% 42.59/42.77  thf('30', plain,
% 42.59/42.77      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.77           (u1_struct_0 @ sk_A))
% 42.59/42.77        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.77      inference('demod', [status(thm)], ['21', '24'])).
% 42.59/42.77  thf('31', plain,
% 42.59/42.77      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 42.59/42.77        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.77      inference('sup-', [status(thm)], ['29', '30'])).
% 42.59/42.78  thf('32', plain,
% 42.59/42.78      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('33', plain,
% 42.59/42.78      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup+', [status(thm)], ['31', '32'])).
% 42.59/42.78  thf('34', plain,
% 42.59/42.78      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.78        (k1_zfmisc_1 @ 
% 42.59/42.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('35', plain,
% 42.59/42.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 42.59/42.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 42.59/42.78  thf('36', plain,
% 42.59/42.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 42.59/42.78         (((X36) != (k1_xboole_0))
% 42.59/42.78          | ((X37) = (k1_xboole_0))
% 42.59/42.78          | ((X38) = (k1_xboole_0))
% 42.59/42.78          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 42.59/42.78          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 42.59/42.78  thf('37', plain,
% 42.59/42.78      (![X37 : $i, X38 : $i]:
% 42.59/42.78         (~ (m1_subset_1 @ X38 @ 
% 42.59/42.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ k1_xboole_0)))
% 42.59/42.78          | ~ (v1_funct_2 @ X38 @ X37 @ k1_xboole_0)
% 42.59/42.78          | ((X38) = (k1_xboole_0))
% 42.59/42.78          | ((X37) = (k1_xboole_0)))),
% 42.59/42.78      inference('simplify', [status(thm)], ['36'])).
% 42.59/42.78  thf('38', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.59/42.78         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 42.59/42.78          | ~ (v1_xboole_0 @ X0)
% 42.59/42.78          | ((X1) = (k1_xboole_0))
% 42.59/42.78          | ((X2) = (k1_xboole_0))
% 42.59/42.78          | ~ (v1_funct_2 @ X2 @ X1 @ k1_xboole_0))),
% 42.59/42.78      inference('sup-', [status(thm)], ['35', '37'])).
% 42.59/42.78  thf('39', plain,
% 42.59/42.78      ((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 42.59/42.78        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['34', '38'])).
% 42.59/42.78  thf('40', plain,
% 42.59/42.78      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['33', '39'])).
% 42.59/42.78  thf('41', plain,
% 42.59/42.78      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['26', '40'])).
% 42.59/42.78  thf('42', plain,
% 42.59/42.78      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('simplify', [status(thm)], ['41'])).
% 42.59/42.78  thf('43', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_A)
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup+', [status(thm)], ['7', '42'])).
% 42.59/42.78  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('45', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 42.59/42.78      inference('demod', [status(thm)], ['43', '44'])).
% 42.59/42.78  thf('46', plain,
% 42.59/42.78      (((zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 42.59/42.78        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['15', '16'])).
% 42.59/42.78  thf('47', plain,
% 42.59/42.78      ((~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ k1_xboole_0)
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78           (u1_struct_0 @ sk_A)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['45', '46'])).
% 42.59/42.78  thf('48', plain,
% 42.59/42.78      (![X31 : $i, X32 : $i]:
% 42.59/42.78         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 42.59/42.78  thf('49', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 42.59/42.78      inference('simplify', [status(thm)], ['48'])).
% 42.59/42.78  thf('50', plain,
% 42.59/42.78      ((((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78           (u1_struct_0 @ sk_A)))),
% 42.59/42.78      inference('demod', [status(thm)], ['47', '49'])).
% 42.59/42.78  thf('51', plain,
% 42.59/42.78      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78           (u1_struct_0 @ sk_A))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('demod', [status(thm)], ['21', '24'])).
% 42.59/42.78  thf('52', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['50', '51'])).
% 42.59/42.78  thf('53', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_A)
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup+', [status(thm)], ['6', '52'])).
% 42.59/42.78  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('55', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('demod', [status(thm)], ['53', '54'])).
% 42.59/42.78  thf('56', plain,
% 42.59/42.78      ((((sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('simplify', [status(thm)], ['55'])).
% 42.59/42.78  thf(t55_funct_1, axiom,
% 42.59/42.78    (![A:$i]:
% 42.59/42.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 42.59/42.78       ( ( v2_funct_1 @ A ) =>
% 42.59/42.78         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 42.59/42.78           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 42.59/42.78  thf('57', plain,
% 42.59/42.78      (![X21 : $i]:
% 42.59/42.78         (~ (v2_funct_1 @ X21)
% 42.59/42.78          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 42.59/42.78          | ~ (v1_funct_1 @ X21)
% 42.59/42.78          | ~ (v1_relat_1 @ X21))),
% 42.59/42.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 42.59/42.78  thf('58', plain,
% 42.59/42.78      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          != (k2_struct_0 @ sk_B_3))
% 42.59/42.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78            != (k2_struct_0 @ sk_A)))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('59', plain,
% 42.59/42.78      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          != (k2_struct_0 @ sk_A)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_A))))),
% 42.59/42.78      inference('split', [status(esa)], ['58'])).
% 42.59/42.78  thf('60', plain,
% 42.59/42.78      (![X42 : $i]:
% 42.59/42.78         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.78  thf('61', plain,
% 42.59/42.78      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.78        (k1_zfmisc_1 @ 
% 42.59/42.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf(d4_tops_2, axiom,
% 42.59/42.78    (![A:$i,B:$i,C:$i]:
% 42.59/42.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 42.59/42.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.59/42.78       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 42.59/42.78         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 42.59/42.78  thf('62', plain,
% 42.59/42.78      (![X47 : $i, X48 : $i, X49 : $i]:
% 42.59/42.78         (((k2_relset_1 @ X48 @ X47 @ X49) != (X47))
% 42.59/42.78          | ~ (v2_funct_1 @ X49)
% 42.59/42.78          | ((k2_tops_2 @ X48 @ X47 @ X49) = (k2_funct_1 @ X49))
% 42.59/42.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 42.59/42.78          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 42.59/42.78          | ~ (v1_funct_1 @ X49))),
% 42.59/42.78      inference('cnf', [status(esa)], [d4_tops_2])).
% 42.59/42.78  thf('63', plain,
% 42.59/42.78      ((~ (v1_funct_1 @ sk_C_1)
% 42.59/42.78        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78             (u1_struct_0 @ sk_B_3))
% 42.59/42.78        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78            = (k2_funct_1 @ sk_C_1))
% 42.59/42.78        | ~ (v2_funct_1 @ sk_C_1)
% 42.59/42.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78            sk_C_1) != (u1_struct_0 @ sk_B_3)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['61', '62'])).
% 42.59/42.78  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('65', plain,
% 42.59/42.78      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('66', plain, ((v2_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('67', plain,
% 42.59/42.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78         = (k2_relat_1 @ sk_C_1))),
% 42.59/42.78      inference('sup-', [status(thm)], ['1', '2'])).
% 42.59/42.78  thf('68', plain,
% 42.59/42.78      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78          = (k2_funct_1 @ sk_C_1))
% 42.59/42.78        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_3)))),
% 42.59/42.78      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 42.59/42.78  thf('69', plain,
% 42.59/42.78      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_3))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_B_3)
% 42.59/42.78        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78            = (k2_funct_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['60', '68'])).
% 42.59/42.78  thf('70', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('sup+', [status(thm)], ['3', '4'])).
% 42.59/42.78  thf('71', plain, ((l1_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('72', plain,
% 42.59/42.78      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 42.59/42.78        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78            = (k2_funct_1 @ sk_C_1)))),
% 42.59/42.78      inference('demod', [status(thm)], ['69', '70', '71'])).
% 42.59/42.78  thf('73', plain,
% 42.59/42.78      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78         = (k2_funct_1 @ sk_C_1))),
% 42.59/42.78      inference('simplify', [status(thm)], ['72'])).
% 42.59/42.78  thf('74', plain,
% 42.59/42.78      (![X42 : $i]:
% 42.59/42.78         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.78  thf('75', plain,
% 42.59/42.78      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.78        (k1_zfmisc_1 @ 
% 42.59/42.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf(t31_funct_2, axiom,
% 42.59/42.78    (![A:$i,B:$i,C:$i]:
% 42.59/42.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 42.59/42.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.59/42.78       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 42.59/42.78         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 42.59/42.78           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 42.59/42.78           ( m1_subset_1 @
% 42.59/42.78             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 42.59/42.78  thf('76', plain,
% 42.59/42.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 42.59/42.78         (~ (v2_funct_1 @ X39)
% 42.59/42.78          | ((k2_relset_1 @ X41 @ X40 @ X39) != (X40))
% 42.59/42.78          | (m1_subset_1 @ (k2_funct_1 @ X39) @ 
% 42.59/42.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 42.59/42.78          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 42.59/42.78          | ~ (v1_funct_2 @ X39 @ X41 @ X40)
% 42.59/42.78          | ~ (v1_funct_1 @ X39))),
% 42.59/42.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 42.59/42.78  thf('77', plain,
% 42.59/42.78      ((~ (v1_funct_1 @ sk_C_1)
% 42.59/42.78        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78             (u1_struct_0 @ sk_B_3))
% 42.59/42.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 42.59/42.78           (k1_zfmisc_1 @ 
% 42.59/42.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))
% 42.59/42.78        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78            sk_C_1) != (u1_struct_0 @ sk_B_3))
% 42.59/42.78        | ~ (v2_funct_1 @ sk_C_1))),
% 42.59/42.78      inference('sup-', [status(thm)], ['75', '76'])).
% 42.59/42.78  thf('78', plain, ((v1_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('79', plain,
% 42.59/42.78      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('80', plain,
% 42.59/42.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78         = (k2_relat_1 @ sk_C_1))),
% 42.59/42.78      inference('sup-', [status(thm)], ['1', '2'])).
% 42.59/42.78  thf('81', plain, ((v2_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('82', plain,
% 42.59/42.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 42.59/42.78         (k1_zfmisc_1 @ 
% 42.59/42.78          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))
% 42.59/42.78        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_3)))),
% 42.59/42.78      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 42.59/42.78  thf('83', plain,
% 42.59/42.78      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_3))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_B_3)
% 42.59/42.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 42.59/42.78           (k1_zfmisc_1 @ 
% 42.59/42.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))))),
% 42.59/42.78      inference('sup-', [status(thm)], ['74', '82'])).
% 42.59/42.78  thf('84', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('sup+', [status(thm)], ['3', '4'])).
% 42.59/42.78  thf('85', plain, ((l1_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('86', plain,
% 42.59/42.78      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 42.59/42.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 42.59/42.78           (k1_zfmisc_1 @ 
% 42.59/42.78            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))))),
% 42.59/42.78      inference('demod', [status(thm)], ['83', '84', '85'])).
% 42.59/42.78  thf('87', plain,
% 42.59/42.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 42.59/42.78        (k1_zfmisc_1 @ 
% 42.59/42.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))),
% 42.59/42.78      inference('simplify', [status(thm)], ['86'])).
% 42.59/42.78  thf('88', plain,
% 42.59/42.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 42.59/42.78         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 42.59/42.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 42.59/42.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 42.59/42.78  thf('89', plain,
% 42.59/42.78      (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78         (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['87', '88'])).
% 42.59/42.78  thf('90', plain,
% 42.59/42.78      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_A))))),
% 42.59/42.78      inference('demod', [status(thm)], ['59', '73', '89'])).
% 42.59/42.78  thf('91', plain,
% 42.59/42.78      (![X21 : $i]:
% 42.59/42.78         (~ (v2_funct_1 @ X21)
% 42.59/42.78          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 42.59/42.78          | ~ (v1_funct_1 @ X21)
% 42.59/42.78          | ~ (v1_relat_1 @ X21))),
% 42.59/42.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 42.59/42.78  thf('92', plain,
% 42.59/42.78      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 42.59/42.78        (k1_zfmisc_1 @ 
% 42.59/42.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))),
% 42.59/42.78      inference('simplify', [status(thm)], ['86'])).
% 42.59/42.78  thf('93', plain,
% 42.59/42.78      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.59/42.78         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 42.59/42.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 42.59/42.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 42.59/42.78  thf('94', plain,
% 42.59/42.78      (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78         (k2_funct_1 @ sk_C_1)) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['92', '93'])).
% 42.59/42.78  thf('95', plain,
% 42.59/42.78      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 42.59/42.78         = (k2_funct_1 @ sk_C_1))),
% 42.59/42.78      inference('simplify', [status(thm)], ['72'])).
% 42.59/42.78  thf('96', plain,
% 42.59/42.78      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          != (k2_struct_0 @ sk_B_3)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('split', [status(esa)], ['58'])).
% 42.59/42.78  thf('97', plain,
% 42.59/42.78      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_B_3)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('sup-', [status(thm)], ['95', '96'])).
% 42.59/42.78  thf('98', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('sup+', [status(thm)], ['3', '4'])).
% 42.59/42.78  thf('99', plain,
% 42.59/42.78      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('demod', [status(thm)], ['97', '98'])).
% 42.59/42.78  thf('100', plain,
% 42.59/42.78      ((((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('sup-', [status(thm)], ['94', '99'])).
% 42.59/42.78  thf('101', plain,
% 42.59/42.78      (((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 42.59/42.78         | ~ (v1_relat_1 @ sk_C_1)
% 42.59/42.78         | ~ (v1_funct_1 @ sk_C_1)
% 42.59/42.78         | ~ (v2_funct_1 @ sk_C_1)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('sup-', [status(thm)], ['91', '100'])).
% 42.59/42.78  thf('102', plain,
% 42.59/42.78      ((m1_subset_1 @ sk_C_1 @ 
% 42.59/42.78        (k1_zfmisc_1 @ 
% 42.59/42.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf(cc1_relset_1, axiom,
% 42.59/42.78    (![A:$i,B:$i,C:$i]:
% 42.59/42.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.59/42.78       ( v1_relat_1 @ C ) ))).
% 42.59/42.78  thf('103', plain,
% 42.59/42.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 42.59/42.78         ((v1_relat_1 @ X22)
% 42.59/42.78          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 42.59/42.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.59/42.78  thf('104', plain, ((v1_relat_1 @ sk_C_1)),
% 42.59/42.78      inference('sup-', [status(thm)], ['102', '103'])).
% 42.59/42.78  thf('105', plain, ((v1_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('106', plain, ((v2_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('107', plain,
% 42.59/42.78      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))
% 42.59/42.78         <= (~
% 42.59/42.78             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 42.59/42.78                 sk_C_1))
% 42.59/42.78                = (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('demod', [status(thm)], ['101', '104', '105', '106'])).
% 42.59/42.78  thf('108', plain,
% 42.59/42.78      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          = (k2_struct_0 @ sk_B_3)))),
% 42.59/42.78      inference('simplify', [status(thm)], ['107'])).
% 42.59/42.78  thf('109', plain,
% 42.59/42.78      (~
% 42.59/42.78       (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          = (k2_struct_0 @ sk_A))) | 
% 42.59/42.78       ~
% 42.59/42.78       (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          = (k2_struct_0 @ sk_B_3)))),
% 42.59/42.78      inference('split', [status(esa)], ['58'])).
% 42.59/42.78  thf('110', plain,
% 42.59/42.78      (~
% 42.59/42.78       (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 42.59/42.78          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 42.59/42.78          = (k2_struct_0 @ sk_A)))),
% 42.59/42.78      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 42.59/42.78  thf('111', plain,
% 42.59/42.78      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A))),
% 42.59/42.78      inference('simpl_trail', [status(thm)], ['90', '110'])).
% 42.59/42.78  thf('112', plain,
% 42.59/42.78      ((((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))
% 42.59/42.78        | ~ (v1_relat_1 @ sk_C_1)
% 42.59/42.78        | ~ (v1_funct_1 @ sk_C_1)
% 42.59/42.78        | ~ (v2_funct_1 @ sk_C_1))),
% 42.59/42.78      inference('sup-', [status(thm)], ['57', '111'])).
% 42.59/42.78  thf('113', plain, ((v1_relat_1 @ sk_C_1)),
% 42.59/42.78      inference('sup-', [status(thm)], ['102', '103'])).
% 42.59/42.78  thf('114', plain, ((v1_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('115', plain, ((v2_funct_1 @ sk_C_1)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('116', plain, (((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 42.59/42.78      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 42.59/42.78  thf('117', plain,
% 42.59/42.78      ((((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((sk_C_1) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['56', '116'])).
% 42.59/42.78  thf('118', plain, (((sk_C_1) = (k1_xboole_0))),
% 42.59/42.78      inference('simplify', [status(thm)], ['117'])).
% 42.59/42.78  thf('119', plain, (((k2_relat_1 @ k1_xboole_0) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('demod', [status(thm)], ['5', '118'])).
% 42.59/42.78  thf('120', plain,
% 42.59/42.78      (![X42 : $i]:
% 42.59/42.78         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.78  thf('121', plain,
% 42.59/42.78      (![X42 : $i]:
% 42.59/42.78         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.78  thf('122', plain,
% 42.59/42.78      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['29', '30'])).
% 42.59/42.78  thf('123', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_B_3) = (k1_xboole_0))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_B_3)
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('sup+', [status(thm)], ['121', '122'])).
% 42.59/42.78  thf('124', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('sup+', [status(thm)], ['3', '4'])).
% 42.59/42.78  thf('125', plain, ((l1_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('126', plain,
% 42.59/42.78      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 42.59/42.78        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 42.59/42.78      inference('demod', [status(thm)], ['123', '124', '125'])).
% 42.59/42.78  thf('127', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_A)
% 42.59/42.78        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup+', [status(thm)], ['120', '126'])).
% 42.59/42.78  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('129', plain,
% 42.59/42.78      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 42.59/42.78      inference('demod', [status(thm)], ['127', '128'])).
% 42.59/42.78  thf('130', plain, (((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 42.59/42.78      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 42.59/42.78  thf('131', plain,
% 42.59/42.78      ((((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))
% 42.59/42.78        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['129', '130'])).
% 42.59/42.78  thf('132', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 42.59/42.78      inference('simplify', [status(thm)], ['131'])).
% 42.59/42.78  thf('133', plain, (((sk_C_1) = (k1_xboole_0))),
% 42.59/42.78      inference('simplify', [status(thm)], ['117'])).
% 42.59/42.78  thf('134', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 42.59/42.78      inference('demod', [status(thm)], ['132', '133'])).
% 42.59/42.78  thf('135', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('demod', [status(thm)], ['119', '134'])).
% 42.59/42.78  thf('136', plain,
% 42.59/42.78      (![X42 : $i]:
% 42.59/42.78         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 42.59/42.78  thf(rc20_struct_0, axiom,
% 42.59/42.78    (![A:$i]:
% 42.59/42.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 42.59/42.78       ( ?[B:$i]:
% 42.59/42.78         ( ( v1_zfmisc_1 @ B ) & ( ~( v1_xboole_0 @ B ) ) & 
% 42.59/42.78           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 42.59/42.78  thf('137', plain,
% 42.59/42.78      (![X43 : $i]:
% 42.59/42.78         ((m1_subset_1 @ (sk_B_1 @ X43) @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 42.59/42.78          | ~ (l1_struct_0 @ X43)
% 42.59/42.78          | (v2_struct_0 @ X43))),
% 42.59/42.78      inference('cnf', [status(esa)], [rc20_struct_0])).
% 42.59/42.78  thf('138', plain,
% 42.59/42.78      (![X0 : $i]:
% 42.59/42.78         ((m1_subset_1 @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 42.59/42.78          | ~ (l1_struct_0 @ X0)
% 42.59/42.78          | (v2_struct_0 @ X0)
% 42.59/42.78          | ~ (l1_struct_0 @ X0))),
% 42.59/42.78      inference('sup+', [status(thm)], ['136', '137'])).
% 42.59/42.78  thf('139', plain,
% 42.59/42.78      (![X0 : $i]:
% 42.59/42.78         ((v2_struct_0 @ X0)
% 42.59/42.78          | ~ (l1_struct_0 @ X0)
% 42.59/42.78          | (m1_subset_1 @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 42.59/42.78      inference('simplify', [status(thm)], ['138'])).
% 42.59/42.78  thf(d2_subset_1, axiom,
% 42.59/42.78    (![A:$i,B:$i]:
% 42.59/42.78     ( ( ( v1_xboole_0 @ A ) =>
% 42.59/42.78         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 42.59/42.78       ( ( ~( v1_xboole_0 @ A ) ) =>
% 42.59/42.78         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 42.59/42.78  thf('140', plain,
% 42.59/42.78      (![X7 : $i, X8 : $i]:
% 42.59/42.78         (~ (m1_subset_1 @ X7 @ X8)
% 42.59/42.78          | (r2_hidden @ X7 @ X8)
% 42.59/42.78          | (v1_xboole_0 @ X8))),
% 42.59/42.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 42.59/42.78  thf('141', plain,
% 42.59/42.78      (![X0 : $i]:
% 42.59/42.78         (~ (l1_struct_0 @ X0)
% 42.59/42.78          | (v2_struct_0 @ X0)
% 42.59/42.78          | (v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 42.59/42.78          | (r2_hidden @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 42.59/42.78      inference('sup-', [status(thm)], ['139', '140'])).
% 42.59/42.78  thf('142', plain,
% 42.59/42.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 42.59/42.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 42.59/42.78  thf(t99_zfmisc_1, axiom,
% 42.59/42.78    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 42.59/42.78  thf('143', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 42.59/42.78      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 42.59/42.78  thf(t91_orders_1, axiom,
% 42.59/42.78    (![A:$i]:
% 42.59/42.78     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 42.59/42.78            ( ![B:$i]:
% 42.59/42.78              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 42.59/42.78       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 42.59/42.78            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 42.59/42.78  thf('144', plain,
% 42.59/42.78      (![X44 : $i, X45 : $i]:
% 42.59/42.78         (((X44) = (k1_xboole_0))
% 42.59/42.78          | ~ (r2_hidden @ X44 @ X45)
% 42.59/42.78          | ((k3_tarski @ X45) != (k1_xboole_0)))),
% 42.59/42.78      inference('cnf', [status(esa)], [t91_orders_1])).
% 42.59/42.78  thf('145', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]:
% 42.59/42.78         (((X0) != (k1_xboole_0))
% 42.59/42.78          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 42.59/42.78          | ((X1) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['143', '144'])).
% 42.59/42.78  thf('146', plain,
% 42.59/42.78      (![X1 : $i]:
% 42.59/42.78         (((X1) = (k1_xboole_0))
% 42.59/42.78          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 42.59/42.78      inference('simplify', [status(thm)], ['145'])).
% 42.59/42.78  thf('147', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]:
% 42.59/42.78         (~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 42.59/42.78          | ~ (v1_xboole_0 @ X0)
% 42.59/42.78          | ((X1) = (k1_xboole_0)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['142', '146'])).
% 42.59/42.78  thf('148', plain,
% 42.59/42.78      (![X0 : $i]:
% 42.59/42.78         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 42.59/42.78          | (v2_struct_0 @ X0)
% 42.59/42.78          | ~ (l1_struct_0 @ X0)
% 42.59/42.78          | ((sk_B_1 @ X0) = (k1_xboole_0))
% 42.59/42.78          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 42.59/42.78      inference('sup-', [status(thm)], ['141', '147'])).
% 42.59/42.78  thf('149', plain,
% 42.59/42.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 42.59/42.78        | ((sk_B_1 @ sk_B_3) = (k1_xboole_0))
% 42.59/42.78        | ~ (l1_struct_0 @ sk_B_3)
% 42.59/42.78        | (v2_struct_0 @ sk_B_3)
% 42.59/42.78        | (v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_3))))),
% 42.59/42.78      inference('sup-', [status(thm)], ['135', '148'])).
% 42.59/42.78  thf('150', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 42.59/42.78      inference('demod', [status(thm)], ['9', '12'])).
% 42.59/42.78  thf('151', plain, ((l1_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('152', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('demod', [status(thm)], ['119', '134'])).
% 42.59/42.78  thf('153', plain,
% 42.59/42.78      ((((sk_B_1 @ sk_B_3) = (k1_xboole_0))
% 42.59/42.78        | (v2_struct_0 @ sk_B_3)
% 42.59/42.78        | (v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 42.59/42.78      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 42.59/42.78  thf('154', plain, (~ (v2_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('155', plain,
% 42.59/42.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 42.59/42.78        | ((sk_B_1 @ sk_B_3) = (k1_xboole_0)))),
% 42.59/42.78      inference('clc', [status(thm)], ['153', '154'])).
% 42.59/42.78  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 42.59/42.78  thf('156', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_subset_1])).
% 42.59/42.78  thf(t38_subset_1, axiom,
% 42.59/42.78    (![A:$i,B:$i]:
% 42.59/42.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 42.59/42.78       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 42.59/42.78         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 42.59/42.78  thf('157', plain,
% 42.59/42.78      (![X16 : $i, X17 : $i]:
% 42.59/42.78         (((X17) != (k1_subset_1 @ X16))
% 42.59/42.78          | (r1_tarski @ X17 @ (k3_subset_1 @ X16 @ X17))
% 42.59/42.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 42.59/42.78      inference('cnf', [status(esa)], [t38_subset_1])).
% 42.59/42.78  thf('158', plain,
% 42.59/42.78      (![X16 : $i]:
% 42.59/42.78         (~ (m1_subset_1 @ (k1_subset_1 @ X16) @ (k1_zfmisc_1 @ X16))
% 42.59/42.78          | (r1_tarski @ (k1_subset_1 @ X16) @ 
% 42.59/42.78             (k3_subset_1 @ X16 @ (k1_subset_1 @ X16))))),
% 42.59/42.78      inference('simplify', [status(thm)], ['157'])).
% 42.59/42.78  thf('159', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_subset_1])).
% 42.59/42.78  thf('160', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 42.59/42.78      inference('cnf', [status(esa)], [d3_subset_1])).
% 42.59/42.78  thf('161', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 42.59/42.78      inference('sup+', [status(thm)], ['159', '160'])).
% 42.59/42.78  thf(dt_k1_subset_1, axiom,
% 42.59/42.78    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 42.59/42.78  thf('162', plain,
% 42.59/42.78      (![X12 : $i]: (m1_subset_1 @ (k1_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 42.59/42.78      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 42.59/42.78  thf('163', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]:
% 42.59/42.78         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 42.59/42.78      inference('sup+', [status(thm)], ['161', '162'])).
% 42.59/42.78  thf('164', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 42.59/42.78      inference('sup+', [status(thm)], ['159', '160'])).
% 42.59/42.78  thf(t22_subset_1, axiom,
% 42.59/42.78    (![A:$i]:
% 42.59/42.78     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 42.59/42.78  thf('165', plain,
% 42.59/42.78      (![X15 : $i]:
% 42.59/42.78         ((k2_subset_1 @ X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 42.59/42.78      inference('cnf', [status(esa)], [t22_subset_1])).
% 42.59/42.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 42.59/42.78  thf('166', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 42.59/42.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 42.59/42.78  thf('167', plain,
% 42.59/42.78      (![X15 : $i]: ((X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 42.59/42.78      inference('demod', [status(thm)], ['165', '166'])).
% 42.59/42.78  thf('168', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 42.59/42.78      inference('sup+', [status(thm)], ['164', '167'])).
% 42.59/42.78  thf('169', plain, (![X16 : $i]: (r1_tarski @ (k1_subset_1 @ X16) @ X16)),
% 42.59/42.78      inference('demod', [status(thm)], ['158', '163', '168'])).
% 42.59/42.78  thf('170', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 42.59/42.78      inference('sup+', [status(thm)], ['156', '169'])).
% 42.59/42.78  thf(d1_zfmisc_1, axiom,
% 42.59/42.78    (![A:$i,B:$i]:
% 42.59/42.78     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 42.59/42.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 42.59/42.78  thf('171', plain,
% 42.59/42.78      (![X1 : $i, X2 : $i, X3 : $i]:
% 42.59/42.78         (~ (r1_tarski @ X1 @ X2)
% 42.59/42.78          | (r2_hidden @ X1 @ X3)
% 42.59/42.78          | ((X3) != (k1_zfmisc_1 @ X2)))),
% 42.59/42.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 42.59/42.78  thf('172', plain,
% 42.59/42.78      (![X1 : $i, X2 : $i]:
% 42.59/42.78         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 42.59/42.78      inference('simplify', [status(thm)], ['171'])).
% 42.59/42.78  thf('173', plain,
% 42.59/42.78      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.59/42.78      inference('sup-', [status(thm)], ['170', '172'])).
% 42.59/42.78  thf(dt_k2_subset_1, axiom,
% 42.59/42.78    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 42.59/42.78  thf('174', plain,
% 42.59/42.78      (![X13 : $i]: (m1_subset_1 @ (k2_subset_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 42.59/42.78      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 42.59/42.78  thf('175', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 42.59/42.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 42.59/42.78  thf('176', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 42.59/42.78      inference('demod', [status(thm)], ['174', '175'])).
% 42.59/42.78  thf(t5_subset, axiom,
% 42.59/42.78    (![A:$i,B:$i,C:$i]:
% 42.59/42.78     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 42.59/42.78          ( v1_xboole_0 @ C ) ) ))).
% 42.59/42.78  thf('177', plain,
% 42.59/42.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 42.59/42.78         (~ (r2_hidden @ X18 @ X19)
% 42.59/42.78          | ~ (v1_xboole_0 @ X20)
% 42.59/42.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 42.59/42.78      inference('cnf', [status(esa)], [t5_subset])).
% 42.59/42.78  thf('178', plain,
% 42.59/42.78      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 42.59/42.78      inference('sup-', [status(thm)], ['176', '177'])).
% 42.59/42.78  thf('179', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 42.59/42.78      inference('sup-', [status(thm)], ['173', '178'])).
% 42.59/42.78  thf('180', plain, (((sk_B_1 @ sk_B_3) = (k1_xboole_0))),
% 42.59/42.78      inference('clc', [status(thm)], ['155', '179'])).
% 42.59/42.78  thf('181', plain,
% 42.59/42.78      (![X43 : $i]:
% 42.59/42.78         (~ (v1_xboole_0 @ (sk_B_1 @ X43))
% 42.59/42.78          | ~ (l1_struct_0 @ X43)
% 42.59/42.78          | (v2_struct_0 @ X43))),
% 42.59/42.78      inference('cnf', [status(esa)], [rc20_struct_0])).
% 42.59/42.78  thf('182', plain,
% 42.59/42.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 42.59/42.78        | (v2_struct_0 @ sk_B_3)
% 42.59/42.78        | ~ (l1_struct_0 @ sk_B_3))),
% 42.59/42.78      inference('sup-', [status(thm)], ['180', '181'])).
% 42.59/42.78  thf('183', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 42.59/42.78      inference('demod', [status(thm)], ['9', '12'])).
% 42.59/42.78  thf('184', plain, ((l1_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.59/42.78  thf('185', plain, ((v2_struct_0 @ sk_B_3)),
% 42.59/42.78      inference('demod', [status(thm)], ['182', '183', '184'])).
% 42.59/42.78  thf('186', plain, ($false), inference('demod', [status(thm)], ['0', '185'])).
% 42.59/42.78  
% 42.59/42.78  % SZS output end Refutation
% 42.59/42.78  
% 42.59/42.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
