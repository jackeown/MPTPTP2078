%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.86ialSiNlG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:53 EST 2020

% Result     : Theorem 32.63s
% Output     : Refutation 32.63s
% Verified   : 
% Statistics : Number of formulae       :  249 (2075 expanded)
%              Number of leaves         :   60 ( 622 expanded)
%              Depth                    :   29
%              Number of atoms          : 2149 (55830 expanded)
%              Number of equality atoms :  208 (3280 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( v1_xboole_0 @ ( sk_B @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('10',plain,(
    ! [X10: $i] :
      ( v1_xboole_0 @ ( sk_B @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
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
    inference(cnf,[status(esa)],[t6_boole])).

thf('36',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
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
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k2_relset_1 @ X50 @ X49 @ X51 )
       != X49 )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_tops_2 @ X50 @ X49 @ X51 )
        = ( k2_funct_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
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

thf('74',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('75',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('76',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v2_funct_1 @ X41 )
      | ( ( k2_relset_1 @ X43 @ X42 @ X41 )
       != X42 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('83',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('87',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('93',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('94',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('96',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( ( ( k2_relat_1 @ sk_C_1 )
       != ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['75','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('101',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['98','101','102','103'])).

thf('105',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_3 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('107',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['74','107'])).

thf('109',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('110',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('111',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('115',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','117'])).

thf('119',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['5','119'])).

thf('121',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,
    ( ( ( u1_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('124',plain,
    ( ( ( k2_struct_0 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('126',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('132',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['118'])).

thf('135',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['120','135'])).

thf('137',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(rc4_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('138',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_struct_0 @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[rc4_struct_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('141',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('144',plain,(
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

thf('145',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( r2_hidden @ X46 @ X47 )
      | ( ( k3_tarski @ X47 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','148'])).

thf('150',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_B_1 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_B_3 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['136','149'])).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('152',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['120','135'])).

thf('154',plain,
    ( ( ( sk_B_1 @ sk_B_3 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_3 )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( sk_B_1 @ sk_B_3 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['154','155'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('157',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('158',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13
       != ( k1_subset_1 @ X12 ) )
      | ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('159',plain,(
    ! [X12: $i] :
      ( ~ ( m1_subset_1 @ ( k1_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ( r1_tarski @ ( k1_subset_1 @ X12 ) @ ( k3_subset_1 @ X12 @ ( k1_subset_1 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('161',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('164',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('166',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = ( k3_subset_1 @ X11 @ ( k1_subset_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('167',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('168',plain,(
    ! [X11: $i] :
      ( X11
      = ( k3_subset_1 @ X11 @ ( k1_subset_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','168'])).

thf('170',plain,(
    ! [X12: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X12 ) @ X12 ) ),
    inference(demod,[status(thm)],['159','162','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['157','170'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('172',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('173',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','173'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('175',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('176',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('177',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('178',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','179'])).

thf('181',plain,
    ( ( sk_B_1 @ sk_B_3 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['156','180'])).

thf('182',plain,(
    ! [X45: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[rc4_struct_0])).

thf('183',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_3 )
    | ~ ( l1_struct_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('185',plain,(
    l1_struct_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_struct_0 @ sk_B_3 ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['0','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.86ialSiNlG
% 0.14/0.36  % Computer   : n019.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:07:23 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 32.63/32.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.63/32.85  % Solved by: fo/fo7.sh
% 32.63/32.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.63/32.85  % done 17870 iterations in 32.398s
% 32.63/32.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.63/32.85  % SZS output start Refutation
% 32.63/32.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 32.63/32.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.63/32.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.63/32.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 32.63/32.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 32.63/32.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 32.63/32.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 32.63/32.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.63/32.85  thf(sk_A_type, type, sk_A: $i).
% 32.63/32.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.63/32.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 32.63/32.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 32.63/32.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.63/32.85  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 32.63/32.85  thf(sk_B_type, type, sk_B: $i > $i).
% 32.63/32.85  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 32.63/32.85  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 32.63/32.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 32.63/32.85  thf(sk_B_3_type, type, sk_B_3: $i).
% 32.63/32.85  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 32.63/32.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.63/32.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 32.63/32.85  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 32.63/32.85  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 32.63/32.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.63/32.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 32.63/32.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 32.63/32.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 32.63/32.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.63/32.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 32.63/32.85  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 32.63/32.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.63/32.85  thf(t62_tops_2, conjecture,
% 32.63/32.85    (![A:$i]:
% 32.63/32.85     ( ( l1_struct_0 @ A ) =>
% 32.63/32.85       ( ![B:$i]:
% 32.63/32.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 32.63/32.85           ( ![C:$i]:
% 32.63/32.85             ( ( ( v1_funct_1 @ C ) & 
% 32.63/32.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 32.63/32.85                 ( m1_subset_1 @
% 32.63/32.85                   C @ 
% 32.63/32.85                   ( k1_zfmisc_1 @
% 32.63/32.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 32.63/32.85               ( ( ( ( k2_relset_1 @
% 32.63/32.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 32.63/32.85                     ( k2_struct_0 @ B ) ) & 
% 32.63/32.85                   ( v2_funct_1 @ C ) ) =>
% 32.63/32.85                 ( ( ( k1_relset_1 @
% 32.63/32.85                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 32.63/32.85                       ( k2_tops_2 @
% 32.63/32.85                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 32.63/32.85                     ( k2_struct_0 @ B ) ) & 
% 32.63/32.85                   ( ( k2_relset_1 @
% 32.63/32.85                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 32.63/32.85                       ( k2_tops_2 @
% 32.63/32.85                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 32.63/32.85                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 32.63/32.85  thf(zf_stmt_0, negated_conjecture,
% 32.63/32.85    (~( ![A:$i]:
% 32.63/32.85        ( ( l1_struct_0 @ A ) =>
% 32.63/32.85          ( ![B:$i]:
% 32.63/32.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 32.63/32.85              ( ![C:$i]:
% 32.63/32.85                ( ( ( v1_funct_1 @ C ) & 
% 32.63/32.85                    ( v1_funct_2 @
% 32.63/32.85                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 32.63/32.85                    ( m1_subset_1 @
% 32.63/32.85                      C @ 
% 32.63/32.85                      ( k1_zfmisc_1 @
% 32.63/32.85                        ( k2_zfmisc_1 @
% 32.63/32.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 32.63/32.85                  ( ( ( ( k2_relset_1 @
% 32.63/32.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 32.63/32.85                        ( k2_struct_0 @ B ) ) & 
% 32.63/32.85                      ( v2_funct_1 @ C ) ) =>
% 32.63/32.85                    ( ( ( k1_relset_1 @
% 32.63/32.85                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 32.63/32.85                          ( k2_tops_2 @
% 32.63/32.85                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 32.63/32.85                        ( k2_struct_0 @ B ) ) & 
% 32.63/32.85                      ( ( k2_relset_1 @
% 32.63/32.85                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 32.63/32.85                          ( k2_tops_2 @
% 32.63/32.85                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 32.63/32.85                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 32.63/32.85    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 32.63/32.85  thf('0', plain, (~ (v2_struct_0 @ sk_B_3)),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.85  thf('1', plain,
% 32.63/32.85      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.85        (k1_zfmisc_1 @ 
% 32.63/32.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.85  thf(redefinition_k2_relset_1, axiom,
% 32.63/32.85    (![A:$i,B:$i,C:$i]:
% 32.63/32.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.63/32.85       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 32.63/32.85  thf('2', plain,
% 32.63/32.85      (![X30 : $i, X31 : $i, X32 : $i]:
% 32.63/32.85         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 32.63/32.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 32.63/32.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.63/32.85  thf('3', plain,
% 32.63/32.85      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.85         = (k2_relat_1 @ sk_C_1))),
% 32.63/32.85      inference('sup-', [status(thm)], ['1', '2'])).
% 32.63/32.85  thf('4', plain,
% 32.63/32.85      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.85         = (k2_struct_0 @ sk_B_3))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.85  thf('5', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.85      inference('sup+', [status(thm)], ['3', '4'])).
% 32.63/32.85  thf(d3_struct_0, axiom,
% 32.63/32.85    (![A:$i]:
% 32.63/32.85     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 32.63/32.85  thf('6', plain,
% 32.63/32.85      (![X44 : $i]:
% 32.63/32.85         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.85  thf('7', plain,
% 32.63/32.85      (![X44 : $i]:
% 32.63/32.85         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.85  thf(d1_funct_2, axiom,
% 32.63/32.85    (![A:$i,B:$i,C:$i]:
% 32.63/32.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.63/32.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 32.63/32.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 32.63/32.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 32.63/32.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.63/32.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 32.63/32.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 32.63/32.85  thf(zf_stmt_1, axiom,
% 32.63/32.85    (![B:$i,A:$i]:
% 32.63/32.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.63/32.85       ( zip_tseitin_0 @ B @ A ) ))).
% 32.63/32.85  thf('8', plain,
% 32.63/32.85      (![X33 : $i, X34 : $i]:
% 32.63/32.85         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 32.63/32.85  thf(rc2_subset_1, axiom,
% 32.63/32.85    (![A:$i]:
% 32.63/32.85     ( ?[B:$i]:
% 32.63/32.85       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 32.63/32.85  thf('9', plain, (![X10 : $i]: (v1_xboole_0 @ (sk_B @ X10))),
% 32.63/32.85      inference('cnf', [status(esa)], [rc2_subset_1])).
% 32.63/32.85  thf('10', plain, (![X10 : $i]: (v1_xboole_0 @ (sk_B @ X10))),
% 32.63/32.85      inference('cnf', [status(esa)], [rc2_subset_1])).
% 32.63/32.85  thf(t6_boole, axiom,
% 32.63/32.85    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 32.63/32.85  thf('11', plain,
% 32.63/32.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 32.63/32.85      inference('cnf', [status(esa)], [t6_boole])).
% 32.63/32.85  thf('12', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 32.63/32.85      inference('sup-', [status(thm)], ['10', '11'])).
% 32.63/32.85  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 32.63/32.85      inference('demod', [status(thm)], ['9', '12'])).
% 32.63/32.85  thf('14', plain,
% 32.63/32.85      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 32.63/32.85      inference('sup+', [status(thm)], ['8', '13'])).
% 32.63/32.85  thf('15', plain,
% 32.63/32.85      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.85        (k1_zfmisc_1 @ 
% 32.63/32.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.85  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 32.63/32.85  thf(zf_stmt_3, axiom,
% 32.63/32.85    (![C:$i,B:$i,A:$i]:
% 32.63/32.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 32.63/32.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 32.63/32.85  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 32.63/32.85  thf(zf_stmt_5, axiom,
% 32.63/32.85    (![A:$i,B:$i,C:$i]:
% 32.63/32.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.63/32.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 32.63/32.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 32.63/32.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 32.63/32.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 32.63/32.85  thf('16', plain,
% 32.63/32.85      (![X38 : $i, X39 : $i, X40 : $i]:
% 32.63/32.85         (~ (zip_tseitin_0 @ X38 @ X39)
% 32.63/32.85          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 32.63/32.85          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 32.63/32.85  thf('17', plain,
% 32.63/32.85      (((zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 32.63/32.85        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))),
% 32.63/32.85      inference('sup-', [status(thm)], ['15', '16'])).
% 32.63/32.85  thf('18', plain,
% 32.63/32.85      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 32.63/32.85        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.85           (u1_struct_0 @ sk_A)))),
% 32.63/32.85      inference('sup-', [status(thm)], ['14', '17'])).
% 32.63/32.85  thf('19', plain,
% 32.63/32.85      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.85  thf('20', plain,
% 32.63/32.85      (![X35 : $i, X36 : $i, X37 : $i]:
% 32.63/32.85         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 32.63/32.85          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 32.63/32.85          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 32.63/32.85  thf('21', plain,
% 32.63/32.85      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.85           (u1_struct_0 @ sk_A))
% 32.63/32.85        | ((u1_struct_0 @ sk_A)
% 32.63/32.85            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.85               sk_C_1)))),
% 32.63/32.85      inference('sup-', [status(thm)], ['19', '20'])).
% 32.63/32.85  thf('22', plain,
% 32.63/32.85      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.85        (k1_zfmisc_1 @ 
% 32.63/32.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.85  thf(redefinition_k1_relset_1, axiom,
% 32.63/32.86    (![A:$i,B:$i,C:$i]:
% 32.63/32.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.63/32.86       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 32.63/32.86  thf('23', plain,
% 32.63/32.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 32.63/32.86         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 32.63/32.86          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 32.63/32.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 32.63/32.86  thf('24', plain,
% 32.63/32.86      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86         = (k1_relat_1 @ sk_C_1))),
% 32.63/32.86      inference('sup-', [status(thm)], ['22', '23'])).
% 32.63/32.86  thf('25', plain,
% 32.63/32.86      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86           (u1_struct_0 @ sk_A))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('demod', [status(thm)], ['21', '24'])).
% 32.63/32.86  thf('26', plain,
% 32.63/32.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['18', '25'])).
% 32.63/32.86  thf('27', plain,
% 32.63/32.86      (![X33 : $i, X34 : $i]:
% 32.63/32.86         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 32.63/32.86  thf('28', plain,
% 32.63/32.86      (((zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 32.63/32.86        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['15', '16'])).
% 32.63/32.86  thf('29', plain,
% 32.63/32.86      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 32.63/32.86        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86           (u1_struct_0 @ sk_A)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['27', '28'])).
% 32.63/32.86  thf('30', plain,
% 32.63/32.86      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86           (u1_struct_0 @ sk_A))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('demod', [status(thm)], ['21', '24'])).
% 32.63/32.86  thf('31', plain,
% 32.63/32.86      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['29', '30'])).
% 32.63/32.86  thf('32', plain,
% 32.63/32.86      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('33', plain,
% 32.63/32.86      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup+', [status(thm)], ['31', '32'])).
% 32.63/32.86  thf('34', plain,
% 32.63/32.86      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.86        (k1_zfmisc_1 @ 
% 32.63/32.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('35', plain,
% 32.63/32.86      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 32.63/32.86      inference('cnf', [status(esa)], [t6_boole])).
% 32.63/32.86  thf('36', plain,
% 32.63/32.86      (![X38 : $i, X39 : $i, X40 : $i]:
% 32.63/32.86         (((X38) != (k1_xboole_0))
% 32.63/32.86          | ((X39) = (k1_xboole_0))
% 32.63/32.86          | ((X40) = (k1_xboole_0))
% 32.63/32.86          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 32.63/32.86          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_5])).
% 32.63/32.86  thf('37', plain,
% 32.63/32.86      (![X39 : $i, X40 : $i]:
% 32.63/32.86         (~ (m1_subset_1 @ X40 @ 
% 32.63/32.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 32.63/32.86          | ~ (v1_funct_2 @ X40 @ X39 @ k1_xboole_0)
% 32.63/32.86          | ((X40) = (k1_xboole_0))
% 32.63/32.86          | ((X39) = (k1_xboole_0)))),
% 32.63/32.86      inference('simplify', [status(thm)], ['36'])).
% 32.63/32.86  thf('38', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.63/32.86         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 32.63/32.86          | ~ (v1_xboole_0 @ X0)
% 32.63/32.86          | ((X1) = (k1_xboole_0))
% 32.63/32.86          | ((X2) = (k1_xboole_0))
% 32.63/32.86          | ~ (v1_funct_2 @ X2 @ X1 @ k1_xboole_0))),
% 32.63/32.86      inference('sup-', [status(thm)], ['35', '37'])).
% 32.63/32.86  thf('39', plain,
% 32.63/32.86      ((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 32.63/32.86        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['34', '38'])).
% 32.63/32.86  thf('40', plain,
% 32.63/32.86      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_3))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['33', '39'])).
% 32.63/32.86  thf('41', plain,
% 32.63/32.86      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['26', '40'])).
% 32.63/32.86  thf('42', plain,
% 32.63/32.86      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('simplify', [status(thm)], ['41'])).
% 32.63/32.86  thf('43', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_A)
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup+', [status(thm)], ['7', '42'])).
% 32.63/32.86  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('45', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 32.63/32.86      inference('demod', [status(thm)], ['43', '44'])).
% 32.63/32.86  thf('46', plain,
% 32.63/32.86      (((zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 32.63/32.86        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['15', '16'])).
% 32.63/32.86  thf('47', plain,
% 32.63/32.86      ((~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B_3) @ k1_xboole_0)
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86           (u1_struct_0 @ sk_A)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['45', '46'])).
% 32.63/32.86  thf('48', plain,
% 32.63/32.86      (![X33 : $i, X34 : $i]:
% 32.63/32.86         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_1])).
% 32.63/32.86  thf('49', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 32.63/32.86      inference('simplify', [status(thm)], ['48'])).
% 32.63/32.86  thf('50', plain,
% 32.63/32.86      ((((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86           (u1_struct_0 @ sk_A)))),
% 32.63/32.86      inference('demod', [status(thm)], ['47', '49'])).
% 32.63/32.86  thf('51', plain,
% 32.63/32.86      ((~ (zip_tseitin_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86           (u1_struct_0 @ sk_A))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('demod', [status(thm)], ['21', '24'])).
% 32.63/32.86  thf('52', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['50', '51'])).
% 32.63/32.86  thf('53', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_A)
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup+', [status(thm)], ['6', '52'])).
% 32.63/32.86  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('55', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('demod', [status(thm)], ['53', '54'])).
% 32.63/32.86  thf('56', plain,
% 32.63/32.86      ((((sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('simplify', [status(thm)], ['55'])).
% 32.63/32.86  thf(t55_funct_1, axiom,
% 32.63/32.86    (![A:$i]:
% 32.63/32.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.63/32.86       ( ( v2_funct_1 @ A ) =>
% 32.63/32.86         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 32.63/32.86           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 32.63/32.86  thf('57', plain,
% 32.63/32.86      (![X23 : $i]:
% 32.63/32.86         (~ (v2_funct_1 @ X23)
% 32.63/32.86          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 32.63/32.86          | ~ (v1_funct_1 @ X23)
% 32.63/32.86          | ~ (v1_relat_1 @ X23))),
% 32.63/32.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.63/32.86  thf('58', plain,
% 32.63/32.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          != (k2_struct_0 @ sk_B_3))
% 32.63/32.86        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86            != (k2_struct_0 @ sk_A)))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('59', plain,
% 32.63/32.86      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          != (k2_struct_0 @ sk_A)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_A))))),
% 32.63/32.86      inference('split', [status(esa)], ['58'])).
% 32.63/32.86  thf('60', plain,
% 32.63/32.86      (![X44 : $i]:
% 32.63/32.86         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.86  thf('61', plain,
% 32.63/32.86      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.86        (k1_zfmisc_1 @ 
% 32.63/32.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf(d4_tops_2, axiom,
% 32.63/32.86    (![A:$i,B:$i,C:$i]:
% 32.63/32.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.63/32.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.63/32.86       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 32.63/32.86         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 32.63/32.86  thf('62', plain,
% 32.63/32.86      (![X49 : $i, X50 : $i, X51 : $i]:
% 32.63/32.86         (((k2_relset_1 @ X50 @ X49 @ X51) != (X49))
% 32.63/32.86          | ~ (v2_funct_1 @ X51)
% 32.63/32.86          | ((k2_tops_2 @ X50 @ X49 @ X51) = (k2_funct_1 @ X51))
% 32.63/32.86          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 32.63/32.86          | ~ (v1_funct_2 @ X51 @ X50 @ X49)
% 32.63/32.86          | ~ (v1_funct_1 @ X51))),
% 32.63/32.86      inference('cnf', [status(esa)], [d4_tops_2])).
% 32.63/32.86  thf('63', plain,
% 32.63/32.86      ((~ (v1_funct_1 @ sk_C_1)
% 32.63/32.86        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86             (u1_struct_0 @ sk_B_3))
% 32.63/32.86        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86            = (k2_funct_1 @ sk_C_1))
% 32.63/32.86        | ~ (v2_funct_1 @ sk_C_1)
% 32.63/32.86        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86            sk_C_1) != (u1_struct_0 @ sk_B_3)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['61', '62'])).
% 32.63/32.86  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('65', plain,
% 32.63/32.86      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('66', plain, ((v2_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('67', plain,
% 32.63/32.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86         = (k2_relat_1 @ sk_C_1))),
% 32.63/32.86      inference('sup-', [status(thm)], ['1', '2'])).
% 32.63/32.86  thf('68', plain,
% 32.63/32.86      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86          = (k2_funct_1 @ sk_C_1))
% 32.63/32.86        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_3)))),
% 32.63/32.86      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 32.63/32.86  thf('69', plain,
% 32.63/32.86      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_3))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_B_3)
% 32.63/32.86        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86            = (k2_funct_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['60', '68'])).
% 32.63/32.86  thf('70', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('sup+', [status(thm)], ['3', '4'])).
% 32.63/32.86  thf('71', plain, ((l1_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('72', plain,
% 32.63/32.86      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 32.63/32.86        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86            = (k2_funct_1 @ sk_C_1)))),
% 32.63/32.86      inference('demod', [status(thm)], ['69', '70', '71'])).
% 32.63/32.86  thf('73', plain,
% 32.63/32.86      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86         = (k2_funct_1 @ sk_C_1))),
% 32.63/32.86      inference('simplify', [status(thm)], ['72'])).
% 32.63/32.86  thf('74', plain,
% 32.63/32.86      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_A))))),
% 32.63/32.86      inference('demod', [status(thm)], ['59', '73'])).
% 32.63/32.86  thf('75', plain,
% 32.63/32.86      (![X23 : $i]:
% 32.63/32.86         (~ (v2_funct_1 @ X23)
% 32.63/32.86          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 32.63/32.86          | ~ (v1_funct_1 @ X23)
% 32.63/32.86          | ~ (v1_relat_1 @ X23))),
% 32.63/32.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.63/32.86  thf('76', plain,
% 32.63/32.86      (![X44 : $i]:
% 32.63/32.86         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.86  thf('77', plain,
% 32.63/32.86      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.86        (k1_zfmisc_1 @ 
% 32.63/32.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf(t31_funct_2, axiom,
% 32.63/32.86    (![A:$i,B:$i,C:$i]:
% 32.63/32.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.63/32.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.63/32.86       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 32.63/32.86         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 32.63/32.86           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 32.63/32.86           ( m1_subset_1 @
% 32.63/32.86             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 32.63/32.86  thf('78', plain,
% 32.63/32.86      (![X41 : $i, X42 : $i, X43 : $i]:
% 32.63/32.86         (~ (v2_funct_1 @ X41)
% 32.63/32.86          | ((k2_relset_1 @ X43 @ X42 @ X41) != (X42))
% 32.63/32.86          | (m1_subset_1 @ (k2_funct_1 @ X41) @ 
% 32.63/32.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 32.63/32.86          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 32.63/32.86          | ~ (v1_funct_2 @ X41 @ X43 @ X42)
% 32.63/32.86          | ~ (v1_funct_1 @ X41))),
% 32.63/32.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 32.63/32.86  thf('79', plain,
% 32.63/32.86      ((~ (v1_funct_1 @ sk_C_1)
% 32.63/32.86        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86             (u1_struct_0 @ sk_B_3))
% 32.63/32.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 32.63/32.86           (k1_zfmisc_1 @ 
% 32.63/32.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))
% 32.63/32.86        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86            sk_C_1) != (u1_struct_0 @ sk_B_3))
% 32.63/32.86        | ~ (v2_funct_1 @ sk_C_1))),
% 32.63/32.86      inference('sup-', [status(thm)], ['77', '78'])).
% 32.63/32.86  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('81', plain,
% 32.63/32.86      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('82', plain,
% 32.63/32.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86         = (k2_relat_1 @ sk_C_1))),
% 32.63/32.86      inference('sup-', [status(thm)], ['1', '2'])).
% 32.63/32.86  thf('83', plain, ((v2_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('84', plain,
% 32.63/32.86      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 32.63/32.86         (k1_zfmisc_1 @ 
% 32.63/32.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))
% 32.63/32.86        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_3)))),
% 32.63/32.86      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 32.63/32.86  thf('85', plain,
% 32.63/32.86      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_3))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_B_3)
% 32.63/32.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 32.63/32.86           (k1_zfmisc_1 @ 
% 32.63/32.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))))),
% 32.63/32.86      inference('sup-', [status(thm)], ['76', '84'])).
% 32.63/32.86  thf('86', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('sup+', [status(thm)], ['3', '4'])).
% 32.63/32.86  thf('87', plain, ((l1_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('88', plain,
% 32.63/32.86      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 32.63/32.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 32.63/32.86           (k1_zfmisc_1 @ 
% 32.63/32.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A)))))),
% 32.63/32.86      inference('demod', [status(thm)], ['85', '86', '87'])).
% 32.63/32.86  thf('89', plain,
% 32.63/32.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 32.63/32.86        (k1_zfmisc_1 @ 
% 32.63/32.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))),
% 32.63/32.86      inference('simplify', [status(thm)], ['88'])).
% 32.63/32.86  thf('90', plain,
% 32.63/32.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 32.63/32.86         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 32.63/32.86          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 32.63/32.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 32.63/32.86  thf('91', plain,
% 32.63/32.86      (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86         (k2_funct_1 @ sk_C_1)) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['89', '90'])).
% 32.63/32.86  thf('92', plain,
% 32.63/32.86      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1)
% 32.63/32.86         = (k2_funct_1 @ sk_C_1))),
% 32.63/32.86      inference('simplify', [status(thm)], ['72'])).
% 32.63/32.86  thf('93', plain,
% 32.63/32.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          != (k2_struct_0 @ sk_B_3)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('split', [status(esa)], ['58'])).
% 32.63/32.86  thf('94', plain,
% 32.63/32.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_B_3)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('sup-', [status(thm)], ['92', '93'])).
% 32.63/32.86  thf('95', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('sup+', [status(thm)], ['3', '4'])).
% 32.63/32.86  thf('96', plain,
% 32.63/32.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('demod', [status(thm)], ['94', '95'])).
% 32.63/32.86  thf('97', plain,
% 32.63/32.86      ((((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('sup-', [status(thm)], ['91', '96'])).
% 32.63/32.86  thf('98', plain,
% 32.63/32.86      (((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 32.63/32.86         | ~ (v1_relat_1 @ sk_C_1)
% 32.63/32.86         | ~ (v1_funct_1 @ sk_C_1)
% 32.63/32.86         | ~ (v2_funct_1 @ sk_C_1)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('sup-', [status(thm)], ['75', '97'])).
% 32.63/32.86  thf('99', plain,
% 32.63/32.86      ((m1_subset_1 @ sk_C_1 @ 
% 32.63/32.86        (k1_zfmisc_1 @ 
% 32.63/32.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf(cc1_relset_1, axiom,
% 32.63/32.86    (![A:$i,B:$i,C:$i]:
% 32.63/32.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.63/32.86       ( v1_relat_1 @ C ) ))).
% 32.63/32.86  thf('100', plain,
% 32.63/32.86      (![X24 : $i, X25 : $i, X26 : $i]:
% 32.63/32.86         ((v1_relat_1 @ X24)
% 32.63/32.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 32.63/32.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.63/32.86  thf('101', plain, ((v1_relat_1 @ sk_C_1)),
% 32.63/32.86      inference('sup-', [status(thm)], ['99', '100'])).
% 32.63/32.86  thf('102', plain, ((v1_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('103', plain, ((v2_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('104', plain,
% 32.63/32.86      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))
% 32.63/32.86         <= (~
% 32.63/32.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 32.63/32.86                 sk_C_1))
% 32.63/32.86                = (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('demod', [status(thm)], ['98', '101', '102', '103'])).
% 32.63/32.86  thf('105', plain,
% 32.63/32.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          = (k2_struct_0 @ sk_B_3)))),
% 32.63/32.86      inference('simplify', [status(thm)], ['104'])).
% 32.63/32.86  thf('106', plain,
% 32.63/32.86      (~
% 32.63/32.86       (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          = (k2_struct_0 @ sk_A))) | 
% 32.63/32.86       ~
% 32.63/32.86       (((k1_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          = (k2_struct_0 @ sk_B_3)))),
% 32.63/32.86      inference('split', [status(esa)], ['58'])).
% 32.63/32.86  thf('107', plain,
% 32.63/32.86      (~
% 32.63/32.86       (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ sk_C_1))
% 32.63/32.86          = (k2_struct_0 @ sk_A)))),
% 32.63/32.86      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 32.63/32.86  thf('108', plain,
% 32.63/32.86      (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86         (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A))),
% 32.63/32.86      inference('simpl_trail', [status(thm)], ['74', '107'])).
% 32.63/32.86  thf('109', plain,
% 32.63/32.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 32.63/32.86        (k1_zfmisc_1 @ 
% 32.63/32.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A))))),
% 32.63/32.86      inference('simplify', [status(thm)], ['88'])).
% 32.63/32.86  thf('110', plain,
% 32.63/32.86      (![X30 : $i, X31 : $i, X32 : $i]:
% 32.63/32.86         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 32.63/32.86          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 32.63/32.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.63/32.86  thf('111', plain,
% 32.63/32.86      (((k2_relset_1 @ (u1_struct_0 @ sk_B_3) @ (u1_struct_0 @ sk_A) @ 
% 32.63/32.86         (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['109', '110'])).
% 32.63/32.86  thf('112', plain,
% 32.63/32.86      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A))),
% 32.63/32.86      inference('demod', [status(thm)], ['108', '111'])).
% 32.63/32.86  thf('113', plain,
% 32.63/32.86      ((((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))
% 32.63/32.86        | ~ (v1_relat_1 @ sk_C_1)
% 32.63/32.86        | ~ (v1_funct_1 @ sk_C_1)
% 32.63/32.86        | ~ (v2_funct_1 @ sk_C_1))),
% 32.63/32.86      inference('sup-', [status(thm)], ['57', '112'])).
% 32.63/32.86  thf('114', plain, ((v1_relat_1 @ sk_C_1)),
% 32.63/32.86      inference('sup-', [status(thm)], ['99', '100'])).
% 32.63/32.86  thf('115', plain, ((v1_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('116', plain, ((v2_funct_1 @ sk_C_1)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('117', plain, (((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 32.63/32.86      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 32.63/32.86  thf('118', plain,
% 32.63/32.86      ((((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((sk_C_1) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['56', '117'])).
% 32.63/32.86  thf('119', plain, (((sk_C_1) = (k1_xboole_0))),
% 32.63/32.86      inference('simplify', [status(thm)], ['118'])).
% 32.63/32.86  thf('120', plain, (((k2_relat_1 @ k1_xboole_0) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('demod', [status(thm)], ['5', '119'])).
% 32.63/32.86  thf('121', plain,
% 32.63/32.86      (![X44 : $i]:
% 32.63/32.86         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.86  thf('122', plain,
% 32.63/32.86      (![X44 : $i]:
% 32.63/32.86         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.86  thf('123', plain,
% 32.63/32.86      ((((u1_struct_0 @ sk_B_3) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['29', '30'])).
% 32.63/32.86  thf('124', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_B_3) = (k1_xboole_0))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_B_3)
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('sup+', [status(thm)], ['122', '123'])).
% 32.63/32.86  thf('125', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('sup+', [status(thm)], ['3', '4'])).
% 32.63/32.86  thf('126', plain, ((l1_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('127', plain,
% 32.63/32.86      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 32.63/32.86        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1)))),
% 32.63/32.86      inference('demod', [status(thm)], ['124', '125', '126'])).
% 32.63/32.86  thf('128', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_A)
% 32.63/32.86        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup+', [status(thm)], ['121', '127'])).
% 32.63/32.86  thf('129', plain, ((l1_struct_0 @ sk_A)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('130', plain,
% 32.63/32.86      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 32.63/32.86      inference('demod', [status(thm)], ['128', '129'])).
% 32.63/32.86  thf('131', plain, (((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 32.63/32.86      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 32.63/32.86  thf('132', plain,
% 32.63/32.86      ((((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))
% 32.63/32.86        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['130', '131'])).
% 32.63/32.86  thf('133', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 32.63/32.86      inference('simplify', [status(thm)], ['132'])).
% 32.63/32.86  thf('134', plain, (((sk_C_1) = (k1_xboole_0))),
% 32.63/32.86      inference('simplify', [status(thm)], ['118'])).
% 32.63/32.86  thf('135', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 32.63/32.86      inference('demod', [status(thm)], ['133', '134'])).
% 32.63/32.86  thf('136', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('demod', [status(thm)], ['120', '135'])).
% 32.63/32.86  thf('137', plain,
% 32.63/32.86      (![X44 : $i]:
% 32.63/32.86         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 32.63/32.86  thf(rc4_struct_0, axiom,
% 32.63/32.86    (![A:$i]:
% 32.63/32.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 32.63/32.86       ( ?[B:$i]:
% 32.63/32.86         ( ( ~( v1_xboole_0 @ B ) ) & 
% 32.63/32.86           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 32.63/32.86  thf('138', plain,
% 32.63/32.86      (![X45 : $i]:
% 32.63/32.86         ((m1_subset_1 @ (sk_B_1 @ X45) @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 32.63/32.86          | ~ (l1_struct_0 @ X45)
% 32.63/32.86          | (v2_struct_0 @ X45))),
% 32.63/32.86      inference('cnf', [status(esa)], [rc4_struct_0])).
% 32.63/32.86  thf('139', plain,
% 32.63/32.86      (![X0 : $i]:
% 32.63/32.86         ((m1_subset_1 @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 32.63/32.86          | ~ (l1_struct_0 @ X0)
% 32.63/32.86          | (v2_struct_0 @ X0)
% 32.63/32.86          | ~ (l1_struct_0 @ X0))),
% 32.63/32.86      inference('sup+', [status(thm)], ['137', '138'])).
% 32.63/32.86  thf('140', plain,
% 32.63/32.86      (![X0 : $i]:
% 32.63/32.86         ((v2_struct_0 @ X0)
% 32.63/32.86          | ~ (l1_struct_0 @ X0)
% 32.63/32.86          | (m1_subset_1 @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 32.63/32.86      inference('simplify', [status(thm)], ['139'])).
% 32.63/32.86  thf(t2_subset, axiom,
% 32.63/32.86    (![A:$i,B:$i]:
% 32.63/32.86     ( ( m1_subset_1 @ A @ B ) =>
% 32.63/32.86       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 32.63/32.86  thf('141', plain,
% 32.63/32.86      (![X15 : $i, X16 : $i]:
% 32.63/32.86         ((r2_hidden @ X15 @ X16)
% 32.63/32.86          | (v1_xboole_0 @ X16)
% 32.63/32.86          | ~ (m1_subset_1 @ X15 @ X16))),
% 32.63/32.86      inference('cnf', [status(esa)], [t2_subset])).
% 32.63/32.86  thf('142', plain,
% 32.63/32.86      (![X0 : $i]:
% 32.63/32.86         (~ (l1_struct_0 @ X0)
% 32.63/32.86          | (v2_struct_0 @ X0)
% 32.63/32.86          | (v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 32.63/32.86          | (r2_hidden @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 32.63/32.86      inference('sup-', [status(thm)], ['140', '141'])).
% 32.63/32.86  thf('143', plain,
% 32.63/32.86      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 32.63/32.86      inference('cnf', [status(esa)], [t6_boole])).
% 32.63/32.86  thf(t99_zfmisc_1, axiom,
% 32.63/32.86    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 32.63/32.86  thf('144', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 32.63/32.86      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 32.63/32.86  thf(t91_orders_1, axiom,
% 32.63/32.86    (![A:$i]:
% 32.63/32.86     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 32.63/32.86            ( ![B:$i]:
% 32.63/32.86              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 32.63/32.86       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 32.63/32.86            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 32.63/32.86  thf('145', plain,
% 32.63/32.86      (![X46 : $i, X47 : $i]:
% 32.63/32.86         (((X46) = (k1_xboole_0))
% 32.63/32.86          | ~ (r2_hidden @ X46 @ X47)
% 32.63/32.86          | ((k3_tarski @ X47) != (k1_xboole_0)))),
% 32.63/32.86      inference('cnf', [status(esa)], [t91_orders_1])).
% 32.63/32.86  thf('146', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i]:
% 32.63/32.86         (((X0) != (k1_xboole_0))
% 32.63/32.86          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 32.63/32.86          | ((X1) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['144', '145'])).
% 32.63/32.86  thf('147', plain,
% 32.63/32.86      (![X1 : $i]:
% 32.63/32.86         (((X1) = (k1_xboole_0))
% 32.63/32.86          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 32.63/32.86      inference('simplify', [status(thm)], ['146'])).
% 32.63/32.86  thf('148', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i]:
% 32.63/32.86         (~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 32.63/32.86          | ~ (v1_xboole_0 @ X0)
% 32.63/32.86          | ((X1) = (k1_xboole_0)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['143', '147'])).
% 32.63/32.86  thf('149', plain,
% 32.63/32.86      (![X0 : $i]:
% 32.63/32.86         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 32.63/32.86          | (v2_struct_0 @ X0)
% 32.63/32.86          | ~ (l1_struct_0 @ X0)
% 32.63/32.86          | ((sk_B_1 @ X0) = (k1_xboole_0))
% 32.63/32.86          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 32.63/32.86      inference('sup-', [status(thm)], ['142', '148'])).
% 32.63/32.86  thf('150', plain,
% 32.63/32.86      ((~ (v1_xboole_0 @ k1_xboole_0)
% 32.63/32.86        | ((sk_B_1 @ sk_B_3) = (k1_xboole_0))
% 32.63/32.86        | ~ (l1_struct_0 @ sk_B_3)
% 32.63/32.86        | (v2_struct_0 @ sk_B_3)
% 32.63/32.86        | (v1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B_3))))),
% 32.63/32.86      inference('sup-', [status(thm)], ['136', '149'])).
% 32.63/32.86  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 32.63/32.86      inference('demod', [status(thm)], ['9', '12'])).
% 32.63/32.86  thf('152', plain, ((l1_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('153', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('demod', [status(thm)], ['120', '135'])).
% 32.63/32.86  thf('154', plain,
% 32.63/32.86      ((((sk_B_1 @ sk_B_3) = (k1_xboole_0))
% 32.63/32.86        | (v2_struct_0 @ sk_B_3)
% 32.63/32.86        | (v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 32.63/32.86      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 32.63/32.86  thf('155', plain, (~ (v2_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('156', plain,
% 32.63/32.86      (((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 32.63/32.86        | ((sk_B_1 @ sk_B_3) = (k1_xboole_0)))),
% 32.63/32.86      inference('clc', [status(thm)], ['154', '155'])).
% 32.63/32.86  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 32.63/32.86  thf('157', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_subset_1])).
% 32.63/32.86  thf(t38_subset_1, axiom,
% 32.63/32.86    (![A:$i,B:$i]:
% 32.63/32.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 32.63/32.86       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 32.63/32.86         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 32.63/32.86  thf('158', plain,
% 32.63/32.86      (![X12 : $i, X13 : $i]:
% 32.63/32.86         (((X13) != (k1_subset_1 @ X12))
% 32.63/32.86          | (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X13))
% 32.63/32.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 32.63/32.86      inference('cnf', [status(esa)], [t38_subset_1])).
% 32.63/32.86  thf('159', plain,
% 32.63/32.86      (![X12 : $i]:
% 32.63/32.86         (~ (m1_subset_1 @ (k1_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))
% 32.63/32.86          | (r1_tarski @ (k1_subset_1 @ X12) @ 
% 32.63/32.86             (k3_subset_1 @ X12 @ (k1_subset_1 @ X12))))),
% 32.63/32.86      inference('simplify', [status(thm)], ['158'])).
% 32.63/32.86  thf('160', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_subset_1])).
% 32.63/32.86  thf(t4_subset_1, axiom,
% 32.63/32.86    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 32.63/32.86  thf('161', plain,
% 32.63/32.86      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 32.63/32.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 32.63/32.86  thf('162', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i]:
% 32.63/32.86         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 32.63/32.86      inference('sup+', [status(thm)], ['160', '161'])).
% 32.63/32.86  thf('163', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_subset_1])).
% 32.63/32.86  thf('164', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 32.63/32.86      inference('cnf', [status(esa)], [d3_subset_1])).
% 32.63/32.86  thf('165', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 32.63/32.86      inference('sup+', [status(thm)], ['163', '164'])).
% 32.63/32.86  thf(t22_subset_1, axiom,
% 32.63/32.86    (![A:$i]:
% 32.63/32.86     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 32.63/32.86  thf('166', plain,
% 32.63/32.86      (![X11 : $i]:
% 32.63/32.86         ((k2_subset_1 @ X11) = (k3_subset_1 @ X11 @ (k1_subset_1 @ X11)))),
% 32.63/32.86      inference('cnf', [status(esa)], [t22_subset_1])).
% 32.63/32.86  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 32.63/32.86  thf('167', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 32.63/32.86      inference('cnf', [status(esa)], [d4_subset_1])).
% 32.63/32.86  thf('168', plain,
% 32.63/32.86      (![X11 : $i]: ((X11) = (k3_subset_1 @ X11 @ (k1_subset_1 @ X11)))),
% 32.63/32.86      inference('demod', [status(thm)], ['166', '167'])).
% 32.63/32.86  thf('169', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 32.63/32.86      inference('sup+', [status(thm)], ['165', '168'])).
% 32.63/32.86  thf('170', plain, (![X12 : $i]: (r1_tarski @ (k1_subset_1 @ X12) @ X12)),
% 32.63/32.86      inference('demod', [status(thm)], ['159', '162', '169'])).
% 32.63/32.86  thf('171', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 32.63/32.86      inference('sup+', [status(thm)], ['157', '170'])).
% 32.63/32.86  thf(d1_zfmisc_1, axiom,
% 32.63/32.86    (![A:$i,B:$i]:
% 32.63/32.86     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 32.63/32.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 32.63/32.86  thf('172', plain,
% 32.63/32.86      (![X1 : $i, X2 : $i, X3 : $i]:
% 32.63/32.86         (~ (r1_tarski @ X1 @ X2)
% 32.63/32.86          | (r2_hidden @ X1 @ X3)
% 32.63/32.86          | ((X3) != (k1_zfmisc_1 @ X2)))),
% 32.63/32.86      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 32.63/32.86  thf('173', plain,
% 32.63/32.86      (![X1 : $i, X2 : $i]:
% 32.63/32.86         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 32.63/32.86      inference('simplify', [status(thm)], ['172'])).
% 32.63/32.86  thf('174', plain,
% 32.63/32.86      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 32.63/32.86      inference('sup-', [status(thm)], ['171', '173'])).
% 32.63/32.86  thf(dt_k2_subset_1, axiom,
% 32.63/32.86    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 32.63/32.86  thf('175', plain,
% 32.63/32.86      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 32.63/32.86      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 32.63/32.86  thf('176', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 32.63/32.86      inference('cnf', [status(esa)], [d4_subset_1])).
% 32.63/32.86  thf('177', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 32.63/32.86      inference('demod', [status(thm)], ['175', '176'])).
% 32.63/32.86  thf(t5_subset, axiom,
% 32.63/32.86    (![A:$i,B:$i,C:$i]:
% 32.63/32.86     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 32.63/32.86          ( v1_xboole_0 @ C ) ) ))).
% 32.63/32.86  thf('178', plain,
% 32.63/32.86      (![X20 : $i, X21 : $i, X22 : $i]:
% 32.63/32.86         (~ (r2_hidden @ X20 @ X21)
% 32.63/32.86          | ~ (v1_xboole_0 @ X22)
% 32.63/32.86          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 32.63/32.86      inference('cnf', [status(esa)], [t5_subset])).
% 32.63/32.86  thf('179', plain,
% 32.63/32.86      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 32.63/32.86      inference('sup-', [status(thm)], ['177', '178'])).
% 32.63/32.86  thf('180', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 32.63/32.86      inference('sup-', [status(thm)], ['174', '179'])).
% 32.63/32.86  thf('181', plain, (((sk_B_1 @ sk_B_3) = (k1_xboole_0))),
% 32.63/32.86      inference('clc', [status(thm)], ['156', '180'])).
% 32.63/32.86  thf('182', plain,
% 32.63/32.86      (![X45 : $i]:
% 32.63/32.86         (~ (v1_xboole_0 @ (sk_B_1 @ X45))
% 32.63/32.86          | ~ (l1_struct_0 @ X45)
% 32.63/32.86          | (v2_struct_0 @ X45))),
% 32.63/32.86      inference('cnf', [status(esa)], [rc4_struct_0])).
% 32.63/32.86  thf('183', plain,
% 32.63/32.86      ((~ (v1_xboole_0 @ k1_xboole_0)
% 32.63/32.86        | (v2_struct_0 @ sk_B_3)
% 32.63/32.86        | ~ (l1_struct_0 @ sk_B_3))),
% 32.63/32.86      inference('sup-', [status(thm)], ['181', '182'])).
% 32.63/32.86  thf('184', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 32.63/32.86      inference('demod', [status(thm)], ['9', '12'])).
% 32.63/32.86  thf('185', plain, ((l1_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.63/32.86  thf('186', plain, ((v2_struct_0 @ sk_B_3)),
% 32.63/32.86      inference('demod', [status(thm)], ['183', '184', '185'])).
% 32.63/32.86  thf('187', plain, ($false), inference('demod', [status(thm)], ['0', '186'])).
% 32.63/32.86  
% 32.63/32.86  % SZS output end Refutation
% 32.63/32.86  
% 32.63/32.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
