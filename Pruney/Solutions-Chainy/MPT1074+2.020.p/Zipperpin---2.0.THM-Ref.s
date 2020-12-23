%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C2jmMn2wJB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:25 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 704 expanded)
%              Number of leaves         :   49 ( 230 expanded)
%              Depth                    :   24
%              Number of atoms          :  957 (9320 expanded)
%              Number of equality atoms :   43 ( 283 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_2 @ X45 @ X46 @ X47 @ X48 )
      | ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X1 @ X3 @ X2 @ X0 )
      | ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1 ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( v5_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['13','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['10','35','38'])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ X53 )
       != X52 )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X53 @ X54 @ X52 ) @ X53 @ X54 @ X52 )
      | ( zip_tseitin_3 @ X53 @ X54 @ X52 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('41',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( v1_funct_1 @ X53 )
      | ( zip_tseitin_3 @ X53 @ X54 @ ( k1_relat_1 @ X53 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X53 @ X54 @ ( k1_relat_1 @ X53 ) ) @ X53 @ X54 @ ( k1_relat_1 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['10','35','38'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['10','35','38'])).

thf('45',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) @ sk_D_3 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('50',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ X42 )
      | ( ( k3_funct_2 @ X42 @ X43 @ X41 @ X44 )
        = ( k1_funct_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X0 )
        = ( k1_funct_1 @ sk_D_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X0 )
        = ( k1_funct_1 @ sk_D_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X0 )
        = ( k1_funct_1 @ sk_D_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','47'])).

thf('59',plain,(
    ! [X55: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X55 ) @ sk_A )
      | ~ ( m1_subset_1 @ X55 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_2 @ X45 @ X46 @ X47 @ X48 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X46 @ X45 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) @ sk_D_3 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_2 @ sk_D_3 @ X0 @ sk_B ) @ sk_D_3 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('66',plain,
    ( ( zip_tseitin_3 @ sk_D_3 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_3 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    zip_tseitin_3 @ sk_D_3 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( zip_tseitin_3 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('69',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v5_relat_1 @ sk_D_3 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['29','30'])).

thf('75',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['4','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C2jmMn2wJB
% 0.13/0.36  % Computer   : n009.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:20:56 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.21/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.39  % Solved by: fo/fo7.sh
% 1.21/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.39  % done 656 iterations in 0.955s
% 1.21/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.39  % SZS output start Refutation
% 1.21/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.21/1.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.21/1.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.21/1.39  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.21/1.39  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.21/1.39  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 1.21/1.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.21/1.39  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.21/1.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.39  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.21/1.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.39  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 1.21/1.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.21/1.39  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.21/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.39  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.21/1.39  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.21/1.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.21/1.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.21/1.39  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.21/1.39  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.21/1.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.21/1.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.21/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.39  thf(t191_funct_2, conjecture,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.39       ( ![C:$i]:
% 1.21/1.39         ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.21/1.39           ( ![D:$i]:
% 1.21/1.39             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.21/1.39                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.21/1.39               ( ( ![E:$i]:
% 1.21/1.39                   ( ( m1_subset_1 @ E @ B ) =>
% 1.21/1.39                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 1.21/1.39                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 1.21/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.39    (~( ![A:$i,B:$i]:
% 1.21/1.39        ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.39          ( ![C:$i]:
% 1.21/1.39            ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.21/1.39              ( ![D:$i]:
% 1.21/1.39                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.21/1.39                    ( m1_subset_1 @
% 1.21/1.39                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.21/1.39                  ( ( ![E:$i]:
% 1.21/1.39                      ( ( m1_subset_1 @ E @ B ) =>
% 1.21/1.39                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 1.21/1.39                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 1.21/1.39    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 1.21/1.39  thf('0', plain,
% 1.21/1.39      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) @ sk_A)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('1', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(redefinition_k2_relset_1, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.21/1.39  thf('2', plain,
% 1.21/1.39      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.21/1.39         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 1.21/1.39          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.21/1.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.21/1.39  thf('3', plain,
% 1.21/1.39      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('sup-', [status(thm)], ['1', '2'])).
% 1.21/1.39  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_A)),
% 1.21/1.39      inference('demod', [status(thm)], ['0', '3'])).
% 1.21/1.39  thf(t5_funct_2, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 1.21/1.39       ( ( ( ![D:$i]:
% 1.21/1.39             ( ( r2_hidden @ D @ A ) =>
% 1.21/1.39               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 1.21/1.39           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 1.21/1.39         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.21/1.39           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 1.21/1.39  thf(zf_stmt_1, axiom,
% 1.21/1.39    (![D:$i,C:$i,B:$i,A:$i]:
% 1.21/1.39     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 1.21/1.39       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 1.21/1.39  thf('5', plain,
% 1.21/1.39      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.21/1.39         ((zip_tseitin_2 @ X45 @ X46 @ X47 @ X48) | (r2_hidden @ X45 @ X48))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.21/1.39  thf(t1_subset, axiom,
% 1.21/1.39    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.21/1.39  thf('6', plain,
% 1.21/1.39      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.21/1.39      inference('cnf', [status(esa)], [t1_subset])).
% 1.21/1.39  thf('7', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.21/1.39         ((zip_tseitin_2 @ X1 @ X3 @ X2 @ X0) | (m1_subset_1 @ X1 @ X0))),
% 1.21/1.39      inference('sup-', [status(thm)], ['5', '6'])).
% 1.21/1.39  thf('8', plain, ((v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(d1_funct_2, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.39       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.21/1.39           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.21/1.39             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.21/1.39         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.21/1.39           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.21/1.39             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.21/1.39  thf(zf_stmt_2, axiom,
% 1.21/1.39    (![C:$i,B:$i,A:$i]:
% 1.21/1.39     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.21/1.39       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.21/1.39  thf('9', plain,
% 1.21/1.39      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.21/1.39         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.21/1.39          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.21/1.39          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.21/1.39  thf('10', plain,
% 1.21/1.39      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)
% 1.21/1.39        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['8', '9'])).
% 1.21/1.39  thf('11', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.21/1.39  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.21/1.39  thf(zf_stmt_5, axiom,
% 1.21/1.39    (![B:$i,A:$i]:
% 1.21/1.39     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.21/1.39       ( zip_tseitin_0 @ B @ A ) ))).
% 1.21/1.39  thf(zf_stmt_6, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.39       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.21/1.39         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.21/1.39           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.21/1.39             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.21/1.39  thf('12', plain,
% 1.21/1.39      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.21/1.39         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.21/1.39          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.21/1.39          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.21/1.39  thf('13', plain,
% 1.21/1.39      (((zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)
% 1.21/1.39        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 1.21/1.39      inference('sup-', [status(thm)], ['11', '12'])).
% 1.21/1.39  thf('14', plain,
% 1.21/1.39      (![X33 : $i, X34 : $i]:
% 1.21/1.39         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.21/1.39  thf(t113_zfmisc_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.21/1.39       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.21/1.39  thf('15', plain,
% 1.21/1.39      (![X1 : $i, X2 : $i]:
% 1.21/1.39         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.21/1.39  thf('16', plain,
% 1.21/1.39      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.39      inference('simplify', [status(thm)], ['15'])).
% 1.21/1.39  thf('17', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.39         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.21/1.39      inference('sup+', [status(thm)], ['14', '16'])).
% 1.21/1.39  thf('18', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('19', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.21/1.39          | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['17', '18'])).
% 1.21/1.39  thf('20', plain,
% 1.21/1.39      (![X1 : $i, X2 : $i]:
% 1.21/1.39         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.21/1.39  thf('21', plain,
% 1.21/1.39      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 1.21/1.39      inference('simplify', [status(thm)], ['20'])).
% 1.21/1.39  thf(cc2_relset_1, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.39       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.21/1.39  thf('22', plain,
% 1.21/1.39      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.21/1.39         ((v5_relat_1 @ X24 @ X26)
% 1.21/1.39          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.21/1.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.21/1.39  thf('23', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.21/1.39          | (v5_relat_1 @ X1 @ X0))),
% 1.21/1.39      inference('sup-', [status(thm)], ['21', '22'])).
% 1.21/1.39  thf('24', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((zip_tseitin_0 @ sk_C_1 @ X1) | (v5_relat_1 @ sk_D_3 @ X0))),
% 1.21/1.39      inference('sup-', [status(thm)], ['19', '23'])).
% 1.21/1.39  thf(d19_relat_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( v1_relat_1 @ B ) =>
% 1.21/1.39       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.21/1.39  thf('25', plain,
% 1.21/1.39      (![X13 : $i, X14 : $i]:
% 1.21/1.39         (~ (v5_relat_1 @ X13 @ X14)
% 1.21/1.39          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.21/1.39          | ~ (v1_relat_1 @ X13))),
% 1.21/1.39      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.21/1.39  thf('26', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((zip_tseitin_0 @ sk_C_1 @ X1)
% 1.21/1.39          | ~ (v1_relat_1 @ sk_D_3)
% 1.21/1.39          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 1.21/1.39      inference('sup-', [status(thm)], ['24', '25'])).
% 1.21/1.39  thf('27', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(cc2_relat_1, axiom,
% 1.21/1.39    (![A:$i]:
% 1.21/1.39     ( ( v1_relat_1 @ A ) =>
% 1.21/1.39       ( ![B:$i]:
% 1.21/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.21/1.39  thf('28', plain,
% 1.21/1.39      (![X11 : $i, X12 : $i]:
% 1.21/1.39         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.21/1.39          | (v1_relat_1 @ X11)
% 1.21/1.39          | ~ (v1_relat_1 @ X12))),
% 1.21/1.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.21/1.39  thf('29', plain,
% 1.21/1.39      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) | (v1_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('sup-', [status(thm)], ['27', '28'])).
% 1.21/1.39  thf(fc6_relat_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.21/1.39  thf('30', plain,
% 1.21/1.39      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.21/1.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.21/1.39  thf('31', plain, ((v1_relat_1 @ sk_D_3)),
% 1.21/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.21/1.39  thf('32', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((zip_tseitin_0 @ sk_C_1 @ X1)
% 1.21/1.39          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['26', '31'])).
% 1.21/1.39  thf('33', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_A)),
% 1.21/1.39      inference('demod', [status(thm)], ['0', '3'])).
% 1.21/1.39  thf('34', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 1.21/1.39      inference('sup-', [status(thm)], ['32', '33'])).
% 1.21/1.39  thf('35', plain, ((zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)),
% 1.21/1.39      inference('demod', [status(thm)], ['13', '34'])).
% 1.21/1.39  thf('36', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(redefinition_k1_relset_1, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.39       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.21/1.39  thf('37', plain,
% 1.21/1.39      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.21/1.39         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 1.21/1.39          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.21/1.39      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.21/1.39  thf('38', plain,
% 1.21/1.39      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('sup-', [status(thm)], ['36', '37'])).
% 1.21/1.39  thf('39', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('demod', [status(thm)], ['10', '35', '38'])).
% 1.21/1.39  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 1.21/1.39  thf(zf_stmt_8, axiom,
% 1.21/1.39    (![C:$i,B:$i,A:$i]:
% 1.21/1.39     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 1.21/1.39       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.21/1.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.21/1.39  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 1.21/1.39  thf(zf_stmt_10, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.21/1.39       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.21/1.39           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 1.21/1.39         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 1.21/1.39  thf('40', plain,
% 1.21/1.39      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.21/1.39         (((k1_relat_1 @ X53) != (X52))
% 1.21/1.39          | ~ (zip_tseitin_2 @ (sk_D_2 @ X53 @ X54 @ X52) @ X53 @ X54 @ X52)
% 1.21/1.39          | (zip_tseitin_3 @ X53 @ X54 @ X52)
% 1.21/1.39          | ~ (v1_funct_1 @ X53)
% 1.21/1.39          | ~ (v1_relat_1 @ X53))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_10])).
% 1.21/1.39  thf('41', plain,
% 1.21/1.39      (![X53 : $i, X54 : $i]:
% 1.21/1.39         (~ (v1_relat_1 @ X53)
% 1.21/1.39          | ~ (v1_funct_1 @ X53)
% 1.21/1.39          | (zip_tseitin_3 @ X53 @ X54 @ (k1_relat_1 @ X53))
% 1.21/1.39          | ~ (zip_tseitin_2 @ (sk_D_2 @ X53 @ X54 @ (k1_relat_1 @ X53)) @ 
% 1.21/1.39               X53 @ X54 @ (k1_relat_1 @ X53)))),
% 1.21/1.39      inference('simplify', [status(thm)], ['40'])).
% 1.21/1.39  thf('42', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         (~ (zip_tseitin_2 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B) @ sk_D_3 @ X0 @ 
% 1.21/1.39             (k1_relat_1 @ sk_D_3))
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ (k1_relat_1 @ sk_D_3))
% 1.21/1.39          | ~ (v1_funct_1 @ sk_D_3)
% 1.21/1.39          | ~ (v1_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('sup-', [status(thm)], ['39', '41'])).
% 1.21/1.39  thf('43', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('demod', [status(thm)], ['10', '35', '38'])).
% 1.21/1.39  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 1.21/1.39      inference('demod', [status(thm)], ['10', '35', '38'])).
% 1.21/1.39  thf('45', plain, ((v1_funct_1 @ sk_D_3)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('46', plain, ((v1_relat_1 @ sk_D_3)),
% 1.21/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.21/1.39  thf('47', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         (~ (zip_tseitin_2 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B) @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B))),
% 1.21/1.39      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 1.21/1.39  thf('48', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B) @ sk_B)
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B))),
% 1.21/1.39      inference('sup-', [status(thm)], ['7', '47'])).
% 1.21/1.39  thf('49', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(redefinition_k3_funct_2, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.21/1.39     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.21/1.39         ( v1_funct_2 @ C @ A @ B ) & 
% 1.21/1.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.21/1.39         ( m1_subset_1 @ D @ A ) ) =>
% 1.21/1.39       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.21/1.39  thf('50', plain,
% 1.21/1.39      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.21/1.39         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.21/1.39          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.21/1.39          | ~ (v1_funct_1 @ X41)
% 1.21/1.39          | (v1_xboole_0 @ X42)
% 1.21/1.39          | ~ (m1_subset_1 @ X44 @ X42)
% 1.21/1.39          | ((k3_funct_2 @ X42 @ X43 @ X41 @ X44) = (k1_funct_1 @ X41 @ X44)))),
% 1.21/1.39      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.21/1.39  thf('51', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X0)
% 1.21/1.39            = (k1_funct_1 @ sk_D_3 @ X0))
% 1.21/1.39          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.21/1.39          | (v1_xboole_0 @ sk_B)
% 1.21/1.39          | ~ (v1_funct_1 @ sk_D_3)
% 1.21/1.39          | ~ (v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1))),
% 1.21/1.39      inference('sup-', [status(thm)], ['49', '50'])).
% 1.21/1.39  thf('52', plain, ((v1_funct_1 @ sk_D_3)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('53', plain, ((v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('54', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X0)
% 1.21/1.39            = (k1_funct_1 @ sk_D_3 @ X0))
% 1.21/1.39          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.21/1.39          | (v1_xboole_0 @ sk_B))),
% 1.21/1.39      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.21/1.39  thf('55', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('56', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         (~ (m1_subset_1 @ X0 @ sk_B)
% 1.21/1.39          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X0)
% 1.21/1.39              = (k1_funct_1 @ sk_D_3 @ X0)))),
% 1.21/1.39      inference('clc', [status(thm)], ['54', '55'])).
% 1.21/1.39  thf('57', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ 
% 1.21/1.39              (sk_D_2 @ sk_D_3 @ X0 @ sk_B))
% 1.21/1.39              = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['48', '56'])).
% 1.21/1.39  thf('58', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B) @ sk_B)
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B))),
% 1.21/1.39      inference('sup-', [status(thm)], ['7', '47'])).
% 1.21/1.39  thf('59', plain,
% 1.21/1.39      (![X55 : $i]:
% 1.21/1.39         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ X55) @ sk_A)
% 1.21/1.39          | ~ (m1_subset_1 @ X55 @ sk_B))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('60', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | (r2_hidden @ 
% 1.21/1.39             (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_3 @ 
% 1.21/1.39              (sk_D_2 @ sk_D_3 @ X0 @ sk_B)) @ 
% 1.21/1.39             sk_A))),
% 1.21/1.39      inference('sup-', [status(thm)], ['58', '59'])).
% 1.21/1.39  thf('61', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B)) @ 
% 1.21/1.39           sk_A)
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B))),
% 1.21/1.39      inference('sup+', [status(thm)], ['57', '60'])).
% 1.21/1.39  thf('62', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | (r2_hidden @ 
% 1.21/1.39             (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B)) @ sk_A))),
% 1.21/1.39      inference('simplify', [status(thm)], ['61'])).
% 1.21/1.39  thf('63', plain,
% 1.21/1.39      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.21/1.39         ((zip_tseitin_2 @ X45 @ X46 @ X47 @ X48)
% 1.21/1.39          | ~ (r2_hidden @ (k1_funct_1 @ X46 @ X45) @ X47))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.21/1.39  thf('64', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | (zip_tseitin_2 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B) @ sk_D_3 @ sk_A @ X1))),
% 1.21/1.39      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.39  thf('65', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         (~ (zip_tseitin_2 @ (sk_D_2 @ sk_D_3 @ X0 @ sk_B) @ sk_D_3 @ X0 @ sk_B)
% 1.21/1.39          | (zip_tseitin_3 @ sk_D_3 @ X0 @ sk_B))),
% 1.21/1.39      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 1.21/1.39  thf('66', plain,
% 1.21/1.39      (((zip_tseitin_3 @ sk_D_3 @ sk_A @ sk_B)
% 1.21/1.39        | (zip_tseitin_3 @ sk_D_3 @ sk_A @ sk_B))),
% 1.21/1.39      inference('sup-', [status(thm)], ['64', '65'])).
% 1.21/1.39  thf('67', plain, ((zip_tseitin_3 @ sk_D_3 @ sk_A @ sk_B)),
% 1.21/1.39      inference('simplify', [status(thm)], ['66'])).
% 1.21/1.39  thf('68', plain,
% 1.21/1.39      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.21/1.39         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 1.21/1.39          | ~ (zip_tseitin_3 @ X49 @ X50 @ X51))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.21/1.39  thf('69', plain,
% 1.21/1.39      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['67', '68'])).
% 1.21/1.39  thf('70', plain,
% 1.21/1.39      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.21/1.39         ((v5_relat_1 @ X24 @ X26)
% 1.21/1.39          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.21/1.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.21/1.39  thf('71', plain, ((v5_relat_1 @ sk_D_3 @ sk_A)),
% 1.21/1.39      inference('sup-', [status(thm)], ['69', '70'])).
% 1.21/1.39  thf('72', plain,
% 1.21/1.39      (![X13 : $i, X14 : $i]:
% 1.21/1.39         (~ (v5_relat_1 @ X13 @ X14)
% 1.21/1.39          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.21/1.39          | ~ (v1_relat_1 @ X13))),
% 1.21/1.39      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.21/1.39  thf('73', plain,
% 1.21/1.39      ((~ (v1_relat_1 @ sk_D_3) | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_A))),
% 1.21/1.39      inference('sup-', [status(thm)], ['71', '72'])).
% 1.21/1.39  thf('74', plain, ((v1_relat_1 @ sk_D_3)),
% 1.21/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.21/1.39  thf('75', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_A)),
% 1.21/1.39      inference('demod', [status(thm)], ['73', '74'])).
% 1.21/1.39  thf('76', plain, ($false), inference('demod', [status(thm)], ['4', '75'])).
% 1.21/1.39  
% 1.21/1.39  % SZS output end Refutation
% 1.21/1.39  
% 1.21/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
