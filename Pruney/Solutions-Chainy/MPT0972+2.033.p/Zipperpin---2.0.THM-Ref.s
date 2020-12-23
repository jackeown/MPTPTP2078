%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TSAw0Y2fNR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:37 EST 2020

% Result     : Theorem 4.58s
% Output     : Refutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  292 (141797 expanded)
%              Number of leaves         :   33 (40308 expanded)
%              Depth                    :   59
%              Number of atoms          : 2308 (2605864 expanded)
%              Number of equality atoms :  306 (148442 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
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

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( sk_A != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X29: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X29 )
        = ( k1_funct_1 @ sk_D @ X29 ) )
      | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( ( k1_funct_1 @ X8 @ ( sk_C_1 @ X7 @ X8 ) )
       != ( k1_funct_1 @ X7 @ ( sk_C_1 @ X7 @ X8 ) ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['13','55'])).

thf('57',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('67',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('76',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('79',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('82',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('83',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('93',plain,(
    v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('96',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('97',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('98',plain,
    ( ( k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('101',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('104',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('107',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('108',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('109',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','110'])).

thf('112',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('114',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['112','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['115'])).

thf('117',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','116'])).

thf('118',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','117'])).

thf('119',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['104','119'])).

thf('121',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','120'])).

thf('122',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('124',plain,
    ( ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('125',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['115'])).

thf('127',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('129',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['112','114'])).

thf('131',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('138',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_2 = sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('142',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C_2 = sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( sk_C_2 = sk_D )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_C_2 = sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','146'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('148',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_C_2 = sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup+',[status(thm)],['94','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup+',[status(thm)],['85','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_2 = sk_D )
      | ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['153'])).

thf('155',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','64'])).

thf('158',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('159',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['156','159'])).

thf('161',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('164',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('165',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('166',plain,
    ( ( k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('167',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('169',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('170',plain,
    ( ( v1_funct_2 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('172',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('174',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('175',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('176',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['115'])).

thf('178',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['173','178'])).

thf('180',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['172','180'])).

thf('182',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['167','181'])).

thf('183',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('185',plain,
    ( ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('186',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['115'])).

thf('188',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('190',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_C_2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_2 = sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('194',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_C_2 = sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = sk_D )
      | ( sk_C_2 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = k1_xboole_0 )
      | ( sk_C_2 = sk_D )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_C_2 = sk_D )
      | ( sk_C_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['183','198'])).

thf('200',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_C_2 = sk_D )
      | ( sk_C_2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_C_2 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup+',[status(thm)],['164','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ( sk_C_2 = k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_C_2 = sk_D ) ) ),
    inference('sup+',[status(thm)],['163','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_2 = sk_D )
      | ( sk_C_2 = k1_xboole_0 )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['205'])).

thf('207',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['157','158'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C_2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['157','158'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 ) ),
    inference(clc,[status(thm)],['162','212'])).

thf('214',plain,(
    zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['84','213'])).

thf('215',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','214'])).

thf('216',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('217',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('218',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 ) ),
    inference(clc,[status(thm)],['162','212'])).

thf('221',plain,(
    zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['218','221'])).

thf('223',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('226',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['218','221'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['215','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('231',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('235',plain,
    ( ( sk_C_2 = sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['77','235'])).

thf('237',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('238',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('240',plain,
    ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['157','158'])).

thf('242',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['67','242'])).

thf('244',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('245',plain,
    ( ( sk_C_2 = sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('246',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('248',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['240','241'])).

thf('250',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( k1_xboole_0 = sk_D ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['243','251'])).

thf('253',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ),
    inference(demod,[status(thm)],['157','158'])).

thf('254',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['240','241'])).

thf('255',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['240','241'])).

thf('256',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    $false ),
    inference(demod,[status(thm)],['252','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TSAw0Y2fNR
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.58/4.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.58/4.82  % Solved by: fo/fo7.sh
% 4.58/4.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.58/4.82  % done 2375 iterations in 4.311s
% 4.58/4.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.58/4.82  % SZS output start Refutation
% 4.58/4.82  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.58/4.82  thf(sk_D_type, type, sk_D: $i).
% 4.58/4.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.58/4.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.58/4.82  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.58/4.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.58/4.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.58/4.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.58/4.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.58/4.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.58/4.82  thf(sk_A_type, type, sk_A: $i).
% 4.58/4.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.58/4.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.58/4.82  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.58/4.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.58/4.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.58/4.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.58/4.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.58/4.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.58/4.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.58/4.82  thf(t18_funct_2, conjecture,
% 4.58/4.82    (![A:$i,B:$i,C:$i]:
% 4.58/4.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.58/4.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.58/4.82       ( ![D:$i]:
% 4.58/4.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.58/4.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.58/4.82           ( ( ![E:$i]:
% 4.58/4.82               ( ( r2_hidden @ E @ A ) =>
% 4.58/4.82                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.58/4.82             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 4.58/4.82  thf(zf_stmt_0, negated_conjecture,
% 4.58/4.82    (~( ![A:$i,B:$i,C:$i]:
% 4.58/4.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.58/4.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.58/4.82          ( ![D:$i]:
% 4.58/4.82            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.58/4.82                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.58/4.82              ( ( ![E:$i]:
% 4.58/4.82                  ( ( r2_hidden @ E @ A ) =>
% 4.58/4.82                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.58/4.82                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 4.58/4.82    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 4.58/4.82  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf(d1_funct_2, axiom,
% 4.58/4.82    (![A:$i,B:$i,C:$i]:
% 4.58/4.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.58/4.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.58/4.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.58/4.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.58/4.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.58/4.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.58/4.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.58/4.82  thf(zf_stmt_1, axiom,
% 4.58/4.82    (![B:$i,A:$i]:
% 4.58/4.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.58/4.82       ( zip_tseitin_0 @ B @ A ) ))).
% 4.58/4.82  thf('1', plain,
% 4.58/4.82      (![X21 : $i, X22 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.58/4.82  thf('2', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.58/4.82  thf(zf_stmt_3, axiom,
% 4.58/4.82    (![C:$i,B:$i,A:$i]:
% 4.58/4.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.58/4.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.58/4.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.58/4.82  thf(zf_stmt_5, axiom,
% 4.58/4.82    (![A:$i,B:$i,C:$i]:
% 4.58/4.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.58/4.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.58/4.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.58/4.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.58/4.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.58/4.82  thf('3', plain,
% 4.58/4.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.58/4.82         (~ (zip_tseitin_0 @ X26 @ X27)
% 4.58/4.82          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 4.58/4.82          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.58/4.82  thf('4', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['2', '3'])).
% 4.58/4.82  thf('5', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['1', '4'])).
% 4.58/4.82  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('7', plain,
% 4.58/4.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.58/4.82         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 4.58/4.82          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 4.58/4.82          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.58/4.82  thf('8', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['6', '7'])).
% 4.58/4.82  thf('9', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf(redefinition_k1_relset_1, axiom,
% 4.58/4.82    (![A:$i,B:$i,C:$i]:
% 4.58/4.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.58/4.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.58/4.82  thf('10', plain,
% 4.58/4.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.58/4.82         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 4.58/4.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.58/4.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.58/4.82  thf('11', plain,
% 4.58/4.82      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.58/4.82      inference('sup-', [status(thm)], ['9', '10'])).
% 4.58/4.82  thf('12', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['8', '11'])).
% 4.58/4.82  thf('13', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['5', '12'])).
% 4.58/4.82  thf('14', plain,
% 4.58/4.82      (![X21 : $i, X22 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.58/4.82  thf('15', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('16', plain,
% 4.58/4.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.58/4.82         (~ (zip_tseitin_0 @ X26 @ X27)
% 4.58/4.82          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 4.58/4.82          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.58/4.82  thf('17', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['15', '16'])).
% 4.58/4.82  thf('18', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['14', '17'])).
% 4.58/4.82  thf('19', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('20', plain,
% 4.58/4.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.58/4.82         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 4.58/4.82          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 4.58/4.82          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.58/4.82  thf('21', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['19', '20'])).
% 4.58/4.82  thf('22', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('23', plain,
% 4.58/4.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.58/4.82         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 4.58/4.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.58/4.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.58/4.82  thf('24', plain,
% 4.58/4.82      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 4.58/4.82      inference('sup-', [status(thm)], ['22', '23'])).
% 4.58/4.82  thf('25', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('demod', [status(thm)], ['21', '24'])).
% 4.58/4.82  thf('26', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['18', '25'])).
% 4.58/4.82  thf('27', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['5', '12'])).
% 4.58/4.82  thf('28', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['18', '25'])).
% 4.58/4.82  thf(t9_funct_1, axiom,
% 4.58/4.82    (![A:$i]:
% 4.58/4.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.58/4.82       ( ![B:$i]:
% 4.58/4.82         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.58/4.82           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 4.58/4.82               ( ![C:$i]:
% 4.58/4.82                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 4.58/4.82                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 4.58/4.82             ( ( A ) = ( B ) ) ) ) ) ))).
% 4.58/4.82  thf('29', plain,
% 4.58/4.82      (![X7 : $i, X8 : $i]:
% 4.58/4.82         (~ (v1_relat_1 @ X7)
% 4.58/4.82          | ~ (v1_funct_1 @ X7)
% 4.58/4.82          | ((X8) = (X7))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ (k1_relat_1 @ X8))
% 4.58/4.82          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 4.58/4.82          | ~ (v1_funct_1 @ X8)
% 4.58/4.82          | ~ (v1_relat_1 @ X8))),
% 4.58/4.82      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.58/4.82  thf('30', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82          | ~ (v1_relat_1 @ sk_C_2)
% 4.58/4.82          | ~ (v1_funct_1 @ sk_C_2)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['28', '29'])).
% 4.58/4.82  thf('31', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf(cc1_relset_1, axiom,
% 4.58/4.82    (![A:$i,B:$i,C:$i]:
% 4.58/4.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.58/4.82       ( v1_relat_1 @ C ) ))).
% 4.58/4.82  thf('32', plain,
% 4.58/4.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.58/4.82         ((v1_relat_1 @ X11)
% 4.58/4.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 4.58/4.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.58/4.82  thf('33', plain, ((v1_relat_1 @ sk_C_2)),
% 4.58/4.82      inference('sup-', [status(thm)], ['31', '32'])).
% 4.58/4.82  thf('34', plain, ((v1_funct_1 @ sk_C_2)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('35', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('demod', [status(thm)], ['30', '33', '34'])).
% 4.58/4.82  thf('36', plain,
% 4.58/4.82      ((((sk_A) != (sk_A))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ~ (v1_relat_1 @ sk_D)
% 4.58/4.82        | ~ (v1_funct_1 @ sk_D)
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['27', '35'])).
% 4.58/4.82  thf('37', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('38', plain,
% 4.58/4.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.58/4.82         ((v1_relat_1 @ X11)
% 4.58/4.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 4.58/4.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.58/4.82  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 4.58/4.82      inference('sup-', [status(thm)], ['37', '38'])).
% 4.58/4.82  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('41', plain,
% 4.58/4.82      ((((sk_A) != (sk_A))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['36', '39', '40'])).
% 4.58/4.82  thf('42', plain,
% 4.58/4.82      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['41'])).
% 4.58/4.82  thf('43', plain,
% 4.58/4.82      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['26', '42'])).
% 4.58/4.82  thf('44', plain,
% 4.58/4.82      ((((sk_C_2) = (sk_D))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 4.58/4.82      inference('simplify', [status(thm)], ['43'])).
% 4.58/4.82  thf('45', plain,
% 4.58/4.82      (![X29 : $i]:
% 4.58/4.82         (((k1_funct_1 @ sk_C_2 @ X29) = (k1_funct_1 @ sk_D @ X29))
% 4.58/4.82          | ~ (r2_hidden @ X29 @ sk_A))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('46', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.58/4.82            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 4.58/4.82      inference('sup-', [status(thm)], ['44', '45'])).
% 4.58/4.82  thf('47', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.58/4.82            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 4.58/4.82      inference('condensation', [status(thm)], ['46'])).
% 4.58/4.82  thf('48', plain,
% 4.58/4.82      (![X7 : $i, X8 : $i]:
% 4.58/4.82         (~ (v1_relat_1 @ X7)
% 4.58/4.82          | ~ (v1_funct_1 @ X7)
% 4.58/4.82          | ((X8) = (X7))
% 4.58/4.82          | ((k1_funct_1 @ X8 @ (sk_C_1 @ X7 @ X8))
% 4.58/4.82              != (k1_funct_1 @ X7 @ (sk_C_1 @ X7 @ X8)))
% 4.58/4.82          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 4.58/4.82          | ~ (v1_funct_1 @ X8)
% 4.58/4.82          | ~ (v1_relat_1 @ X8))),
% 4.58/4.82      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.58/4.82  thf('49', plain,
% 4.58/4.82      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.58/4.82          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ~ (v1_relat_1 @ sk_C_2)
% 4.58/4.82        | ~ (v1_funct_1 @ sk_C_2)
% 4.58/4.82        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | ~ (v1_funct_1 @ sk_D)
% 4.58/4.82        | ~ (v1_relat_1 @ sk_D))),
% 4.58/4.82      inference('sup-', [status(thm)], ['47', '48'])).
% 4.58/4.82  thf('50', plain, ((v1_relat_1 @ sk_C_2)),
% 4.58/4.82      inference('sup-', [status(thm)], ['31', '32'])).
% 4.58/4.82  thf('51', plain, ((v1_funct_1 @ sk_C_2)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 4.58/4.82      inference('sup-', [status(thm)], ['37', '38'])).
% 4.58/4.82  thf('54', plain,
% 4.58/4.82      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.58/4.82          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 4.58/4.82        | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 4.58/4.82  thf('55', plain,
% 4.58/4.82      ((((sk_C_2) = (sk_D))
% 4.58/4.82        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['54'])).
% 4.58/4.82  thf('56', plain,
% 4.58/4.82      ((((k1_relat_1 @ sk_C_2) != (sk_A))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['13', '55'])).
% 4.58/4.82  thf('57', plain,
% 4.58/4.82      ((((sk_C_2) = (sk_D))
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0))
% 4.58/4.82        | ((k1_relat_1 @ sk_C_2) != (sk_A)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['56'])).
% 4.58/4.82  thf('58', plain,
% 4.58/4.82      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['18', '25'])).
% 4.58/4.82  thf('59', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('clc', [status(thm)], ['57', '58'])).
% 4.58/4.82  thf('60', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('61', plain,
% 4.58/4.82      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)
% 4.58/4.82        | ((sk_B_1) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['59', '60'])).
% 4.58/4.82  thf('62', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf(redefinition_r2_relset_1, axiom,
% 4.58/4.82    (![A:$i,B:$i,C:$i,D:$i]:
% 4.58/4.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.58/4.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.58/4.82       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.58/4.82  thf('63', plain,
% 4.58/4.82      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 4.58/4.82         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 4.58/4.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 4.58/4.82          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 4.58/4.82          | ((X17) != (X20)))),
% 4.58/4.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.58/4.82  thf('64', plain,
% 4.58/4.82      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.58/4.82         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 4.58/4.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.58/4.82      inference('simplify', [status(thm)], ['63'])).
% 4.58/4.82  thf('65', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('sup-', [status(thm)], ['62', '64'])).
% 4.58/4.82  thf('66', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('67', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('demod', [status(thm)], ['0', '66'])).
% 4.58/4.82  thf('68', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('69', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('70', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_C_2 @ 
% 4.58/4.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['68', '69'])).
% 4.58/4.82  thf('71', plain,
% 4.58/4.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.58/4.82         (((X26) != (k1_xboole_0))
% 4.58/4.82          | ((X27) = (k1_xboole_0))
% 4.58/4.82          | ((X28) = (k1_xboole_0))
% 4.58/4.82          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 4.58/4.82          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.58/4.82  thf('72', plain,
% 4.58/4.82      (![X27 : $i, X28 : $i]:
% 4.58/4.82         (~ (m1_subset_1 @ X28 @ 
% 4.58/4.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ k1_xboole_0)))
% 4.58/4.82          | ~ (v1_funct_2 @ X28 @ X27 @ k1_xboole_0)
% 4.58/4.82          | ((X28) = (k1_xboole_0))
% 4.58/4.82          | ((X27) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['71'])).
% 4.58/4.82  thf('73', plain,
% 4.58/4.82      ((((sk_A) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['70', '72'])).
% 4.58/4.82  thf('74', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('75', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('76', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 4.58/4.82      inference('demod', [status(thm)], ['74', '75'])).
% 4.58/4.82  thf('77', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('78', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['8', '11'])).
% 4.58/4.82  thf('79', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('80', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['78', '79'])).
% 4.58/4.82  thf('81', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['2', '3'])).
% 4.58/4.82  thf('82', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('83', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('84', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.58/4.82  thf('85', plain,
% 4.58/4.82      (![X21 : $i, X22 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.58/4.82  thf('86', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('87', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('88', plain,
% 4.58/4.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['86', '87'])).
% 4.58/4.82  thf('89', plain,
% 4.58/4.82      (![X27 : $i, X28 : $i]:
% 4.58/4.82         (~ (m1_subset_1 @ X28 @ 
% 4.58/4.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ k1_xboole_0)))
% 4.58/4.82          | ~ (v1_funct_2 @ X28 @ X27 @ k1_xboole_0)
% 4.58/4.82          | ((X28) = (k1_xboole_0))
% 4.58/4.82          | ((X27) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['71'])).
% 4.58/4.82  thf('90', plain,
% 4.58/4.82      ((((sk_A) = (k1_xboole_0))
% 4.58/4.82        | ((sk_D) = (k1_xboole_0))
% 4.58/4.82        | ~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['88', '89'])).
% 4.58/4.82  thf('91', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('92', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('93', plain, ((v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 4.58/4.82      inference('demod', [status(thm)], ['91', '92'])).
% 4.58/4.82  thf('94', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('95', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('96', plain,
% 4.58/4.82      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 4.58/4.82      inference('sup-', [status(thm)], ['22', '23'])).
% 4.58/4.82  thf('97', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('98', plain,
% 4.58/4.82      (((k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 4.58/4.82      inference('demod', [status(thm)], ['96', '97'])).
% 4.58/4.82  thf('99', plain,
% 4.58/4.82      ((((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2)
% 4.58/4.82          = (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['95', '98'])).
% 4.58/4.82  thf('100', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('101', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 4.58/4.82      inference('demod', [status(thm)], ['74', '75'])).
% 4.58/4.82  thf('102', plain,
% 4.58/4.82      (((v1_funct_2 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['100', '101'])).
% 4.58/4.82  thf('103', plain,
% 4.58/4.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.58/4.82         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 4.58/4.82          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 4.58/4.82          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.58/4.82  thf('104', plain,
% 4.58/4.82      ((((sk_D) = (k1_xboole_0))
% 4.58/4.82        | ~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['102', '103'])).
% 4.58/4.82  thf('105', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('106', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('107', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['15', '16'])).
% 4.58/4.82  thf('108', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('109', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('110', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['107', '108', '109'])).
% 4.58/4.82  thf('111', plain,
% 4.58/4.82      ((~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_D) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['106', '110'])).
% 4.58/4.82  thf('112', plain,
% 4.58/4.82      (![X21 : $i, X22 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.58/4.82  thf('113', plain,
% 4.58/4.82      (![X21 : $i, X22 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.58/4.82  thf('114', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 4.58/4.82      inference('simplify', [status(thm)], ['113'])).
% 4.58/4.82  thf('115', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 4.58/4.82      inference('sup+', [status(thm)], ['112', '114'])).
% 4.58/4.82  thf('116', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 4.58/4.82      inference('eq_fact', [status(thm)], ['115'])).
% 4.58/4.82  thf('117', plain,
% 4.58/4.82      ((((sk_D) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['111', '116'])).
% 4.58/4.82  thf('118', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_D) = (k1_xboole_0))
% 4.58/4.82        | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['105', '117'])).
% 4.58/4.82  thf('119', plain,
% 4.58/4.82      ((((sk_D) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0))),
% 4.58/4.82      inference('simplify', [status(thm)], ['118'])).
% 4.58/4.82  thf('120', plain,
% 4.58/4.82      ((((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2))
% 4.58/4.82        | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('clc', [status(thm)], ['104', '119'])).
% 4.58/4.82  thf('121', plain,
% 4.58/4.82      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_D) = (k1_xboole_0))
% 4.58/4.82        | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['99', '120'])).
% 4.58/4.82  thf('122', plain,
% 4.58/4.82      ((((sk_D) = (k1_xboole_0)) | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['121'])).
% 4.58/4.82  thf('123', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('124', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.58/4.82  thf('125', plain,
% 4.58/4.82      ((~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_D) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['123', '124'])).
% 4.58/4.82  thf('126', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 4.58/4.82      inference('eq_fact', [status(thm)], ['115'])).
% 4.58/4.82  thf('127', plain,
% 4.58/4.82      ((((sk_D) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['125', '126'])).
% 4.58/4.82  thf('128', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['78', '79'])).
% 4.58/4.82  thf('129', plain,
% 4.58/4.82      ((((sk_D) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['127', '128'])).
% 4.58/4.82  thf('130', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 4.58/4.82      inference('sup+', [status(thm)], ['112', '114'])).
% 4.58/4.82  thf('131', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['15', '16'])).
% 4.58/4.82  thf('132', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['130', '131'])).
% 4.58/4.82  thf('133', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('demod', [status(thm)], ['21', '24'])).
% 4.58/4.82  thf('134', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['132', '133'])).
% 4.58/4.82  thf('135', plain,
% 4.58/4.82      (![X7 : $i, X8 : $i]:
% 4.58/4.82         (~ (v1_relat_1 @ X7)
% 4.58/4.82          | ~ (v1_funct_1 @ X7)
% 4.58/4.82          | ((X8) = (X7))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ (k1_relat_1 @ X8))
% 4.58/4.82          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 4.58/4.82          | ~ (v1_funct_1 @ X8)
% 4.58/4.82          | ~ (v1_relat_1 @ X8))),
% 4.58/4.82      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.58/4.82  thf('136', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X1)
% 4.58/4.82          | ~ (v1_relat_1 @ sk_C_2)
% 4.58/4.82          | ~ (v1_funct_1 @ sk_C_2)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['134', '135'])).
% 4.58/4.82  thf('137', plain, ((v1_relat_1 @ sk_C_2)),
% 4.58/4.82      inference('sup-', [status(thm)], ['31', '32'])).
% 4.58/4.82  thf('138', plain, ((v1_funct_1 @ sk_C_2)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('139', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X1)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('demod', [status(thm)], ['136', '137', '138'])).
% 4.58/4.82  thf('140', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (sk_A))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | ~ (v1_relat_1 @ sk_D)
% 4.58/4.82          | ~ (v1_funct_1 @ sk_D)
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['129', '139'])).
% 4.58/4.82  thf('141', plain, ((v1_relat_1 @ sk_D)),
% 4.58/4.82      inference('sup-', [status(thm)], ['37', '38'])).
% 4.58/4.82  thf('142', plain, ((v1_funct_1 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('143', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (sk_A))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0))),
% 4.58/4.82      inference('demod', [status(thm)], ['140', '141', '142'])).
% 4.58/4.82  thf('144', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['143'])).
% 4.58/4.82  thf(d1_xboole_0, axiom,
% 4.58/4.82    (![A:$i]:
% 4.58/4.82     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.58/4.82  thf('145', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.58/4.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.58/4.82  thf('146', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_D) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['144', '145'])).
% 4.58/4.82  thf('147', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['122', '146'])).
% 4.58/4.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.58/4.82  thf('148', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.58/4.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.58/4.82  thf('149', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_D) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['147', '148'])).
% 4.58/4.82  thf('150', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_C_2) = (sk_D))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['149'])).
% 4.58/4.82  thf('151', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['94', '150'])).
% 4.58/4.82  thf('152', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ k1_xboole_0 @ X0))),
% 4.58/4.82      inference('simplify', [status(thm)], ['151'])).
% 4.58/4.82  thf('153', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X0 @ X1)
% 4.58/4.82          | (zip_tseitin_0 @ X0 @ X2)
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['85', '152'])).
% 4.58/4.82  thf('154', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_D) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ X1 @ X0))),
% 4.58/4.82      inference('eq_fact', [status(thm)], ['153'])).
% 4.58/4.82  thf('155', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('demod', [status(thm)], ['0', '66'])).
% 4.58/4.82  thf('156', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)
% 4.58/4.82          | (zip_tseitin_0 @ X1 @ X0)
% 4.58/4.82          | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['154', '155'])).
% 4.58/4.82  thf('157', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('sup-', [status(thm)], ['62', '64'])).
% 4.58/4.82  thf('158', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('159', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('demod', [status(thm)], ['157', '158'])).
% 4.58/4.82  thf('160', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X1 @ X0) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['156', '159'])).
% 4.58/4.82  thf('161', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('demod', [status(thm)], ['0', '66'])).
% 4.58/4.82  thf('162', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ k1_xboole_0)
% 4.58/4.82          | (zip_tseitin_0 @ X1 @ X0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['160', '161'])).
% 4.58/4.82  thf('163', plain,
% 4.58/4.82      (![X21 : $i, X22 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.58/4.82  thf('164', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('165', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('166', plain,
% 4.58/4.82      (((k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 4.58/4.82      inference('demod', [status(thm)], ['96', '97'])).
% 4.58/4.82  thf('167', plain,
% 4.58/4.82      ((((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2)
% 4.58/4.82          = (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['165', '166'])).
% 4.58/4.82  thf('168', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('169', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 4.58/4.82      inference('demod', [status(thm)], ['74', '75'])).
% 4.58/4.82  thf('170', plain,
% 4.58/4.82      (((v1_funct_2 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['168', '169'])).
% 4.58/4.82  thf('171', plain,
% 4.58/4.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.58/4.82         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 4.58/4.82          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 4.58/4.82          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.58/4.82  thf('172', plain,
% 4.58/4.82      ((((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | ~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['170', '171'])).
% 4.58/4.82  thf('173', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('174', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('175', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['107', '108', '109'])).
% 4.58/4.82  thf('176', plain,
% 4.58/4.82      ((~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['174', '175'])).
% 4.58/4.82  thf('177', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 4.58/4.82      inference('eq_fact', [status(thm)], ['115'])).
% 4.58/4.82  thf('178', plain,
% 4.58/4.82      ((((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['176', '177'])).
% 4.58/4.82  thf('179', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['173', '178'])).
% 4.58/4.82  thf('180', plain,
% 4.58/4.82      ((((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0))),
% 4.58/4.82      inference('simplify', [status(thm)], ['179'])).
% 4.58/4.82  thf('181', plain,
% 4.58/4.82      ((((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2))
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('clc', [status(thm)], ['172', '180'])).
% 4.58/4.82  thf('182', plain,
% 4.58/4.82      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_2))
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['167', '181'])).
% 4.58/4.82  thf('183', plain,
% 4.58/4.82      ((((sk_C_2) = (k1_xboole_0)) | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['182'])).
% 4.58/4.82  thf('184', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['73', '76'])).
% 4.58/4.82  thf('185', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.58/4.82  thf('186', plain,
% 4.58/4.82      ((~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['184', '185'])).
% 4.58/4.82  thf('187', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 4.58/4.82      inference('eq_fact', [status(thm)], ['115'])).
% 4.58/4.82  thf('188', plain,
% 4.58/4.82      ((((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['186', '187'])).
% 4.58/4.82  thf('189', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['78', '79'])).
% 4.58/4.82  thf('190', plain,
% 4.58/4.82      ((((sk_C_2) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['188', '189'])).
% 4.58/4.82  thf('191', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X1)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('demod', [status(thm)], ['136', '137', '138'])).
% 4.58/4.82  thf('192', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (sk_A))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | ~ (v1_relat_1 @ sk_D)
% 4.58/4.82          | ~ (v1_funct_1 @ sk_D)
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['190', '191'])).
% 4.58/4.82  thf('193', plain, ((v1_relat_1 @ sk_D)),
% 4.58/4.82      inference('sup-', [status(thm)], ['37', '38'])).
% 4.58/4.82  thf('194', plain, ((v1_funct_1 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('195', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (sk_A))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0))),
% 4.58/4.82      inference('demod', [status(thm)], ['192', '193', '194'])).
% 4.58/4.82  thf('196', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['195'])).
% 4.58/4.82  thf('197', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.58/4.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.58/4.82  thf('198', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['196', '197'])).
% 4.58/4.82  thf('199', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['183', '198'])).
% 4.58/4.82  thf('200', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.58/4.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.58/4.82  thf('201', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['199', '200'])).
% 4.58/4.82  thf('202', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_C_2) = (sk_D))
% 4.58/4.82          | (zip_tseitin_0 @ sk_A @ X0)
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['201'])).
% 4.58/4.82  thf('203', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['164', '202'])).
% 4.58/4.82  thf('204', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ k1_xboole_0 @ X0))),
% 4.58/4.82      inference('simplify', [status(thm)], ['203'])).
% 4.58/4.82  thf('205', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X0 @ X1)
% 4.58/4.82          | (zip_tseitin_0 @ X0 @ X2)
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup+', [status(thm)], ['163', '204'])).
% 4.58/4.82  thf('206', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (((sk_C_2) = (sk_D))
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82          | (zip_tseitin_0 @ X1 @ X0))),
% 4.58/4.82      inference('eq_fact', [status(thm)], ['205'])).
% 4.58/4.82  thf('207', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('demod', [status(thm)], ['0', '66'])).
% 4.58/4.82  thf('208', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)
% 4.58/4.82          | (zip_tseitin_0 @ X1 @ X0)
% 4.58/4.82          | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['206', '207'])).
% 4.58/4.82  thf('209', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('demod', [status(thm)], ['157', '158'])).
% 4.58/4.82  thf('210', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         ((zip_tseitin_0 @ X1 @ X0) | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['208', '209'])).
% 4.58/4.82  thf('211', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('demod', [status(thm)], ['157', '158'])).
% 4.58/4.82  thf('212', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]:
% 4.58/4.82         ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ k1_xboole_0)
% 4.58/4.82          | (zip_tseitin_0 @ X1 @ X0))),
% 4.58/4.82      inference('sup+', [status(thm)], ['210', '211'])).
% 4.58/4.82  thf('213', plain, (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ X1 @ X0)),
% 4.58/4.82      inference('clc', [status(thm)], ['162', '212'])).
% 4.58/4.82  thf('214', plain, ((zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)),
% 4.58/4.82      inference('demod', [status(thm)], ['84', '213'])).
% 4.58/4.82  thf('215', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.58/4.82      inference('demod', [status(thm)], ['80', '214'])).
% 4.58/4.82  thf('216', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('demod', [status(thm)], ['21', '24'])).
% 4.58/4.82  thf('217', plain, (((sk_B_1) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['61', '65'])).
% 4.58/4.82  thf('218', plain,
% 4.58/4.82      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.58/4.82      inference('demod', [status(thm)], ['216', '217'])).
% 4.58/4.82  thf('219', plain,
% 4.58/4.82      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 4.58/4.82        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['107', '108', '109'])).
% 4.58/4.82  thf('220', plain, (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ X1 @ X0)),
% 4.58/4.82      inference('clc', [status(thm)], ['162', '212'])).
% 4.58/4.82  thf('221', plain, ((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)),
% 4.58/4.82      inference('demod', [status(thm)], ['219', '220'])).
% 4.58/4.82  thf('222', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 4.58/4.82      inference('demod', [status(thm)], ['218', '221'])).
% 4.58/4.82  thf('223', plain,
% 4.58/4.82      (![X7 : $i, X8 : $i]:
% 4.58/4.82         (~ (v1_relat_1 @ X7)
% 4.58/4.82          | ~ (v1_funct_1 @ X7)
% 4.58/4.82          | ((X8) = (X7))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ (k1_relat_1 @ X8))
% 4.58/4.82          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 4.58/4.82          | ~ (v1_funct_1 @ X8)
% 4.58/4.82          | ~ (v1_relat_1 @ X8))),
% 4.58/4.82      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.58/4.82  thf('224', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | ~ (v1_relat_1 @ sk_C_2)
% 4.58/4.82          | ~ (v1_funct_1 @ sk_C_2)
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('sup-', [status(thm)], ['222', '223'])).
% 4.58/4.82  thf('225', plain, ((v1_relat_1 @ sk_C_2)),
% 4.58/4.82      inference('sup-', [status(thm)], ['31', '32'])).
% 4.58/4.82  thf('226', plain, ((v1_funct_1 @ sk_C_2)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('227', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 4.58/4.82      inference('demod', [status(thm)], ['218', '221'])).
% 4.58/4.82  thf('228', plain,
% 4.58/4.82      (![X0 : $i]:
% 4.58/4.82         (((sk_A) != (k1_relat_1 @ X0))
% 4.58/4.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 4.58/4.82          | ((sk_C_2) = (X0))
% 4.58/4.82          | ~ (v1_funct_1 @ X0)
% 4.58/4.82          | ~ (v1_relat_1 @ X0))),
% 4.58/4.82      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 4.58/4.82  thf('229', plain,
% 4.58/4.82      ((((sk_A) != (sk_A))
% 4.58/4.82        | ~ (v1_relat_1 @ sk_D)
% 4.58/4.82        | ~ (v1_funct_1 @ sk_D)
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['215', '228'])).
% 4.58/4.82  thf('230', plain, ((v1_relat_1 @ sk_D)),
% 4.58/4.82      inference('sup-', [status(thm)], ['37', '38'])).
% 4.58/4.82  thf('231', plain, ((v1_funct_1 @ sk_D)),
% 4.58/4.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.58/4.82  thf('232', plain,
% 4.58/4.82      ((((sk_A) != (sk_A))
% 4.58/4.82        | ((sk_C_2) = (sk_D))
% 4.58/4.82        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 4.58/4.82      inference('demod', [status(thm)], ['229', '230', '231'])).
% 4.58/4.82  thf('233', plain,
% 4.58/4.82      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('simplify', [status(thm)], ['232'])).
% 4.58/4.82  thf('234', plain,
% 4.58/4.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.58/4.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.58/4.82  thf('235', plain, ((((sk_C_2) = (sk_D)) | ~ (v1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['233', '234'])).
% 4.58/4.82  thf('236', plain,
% 4.58/4.82      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['77', '235'])).
% 4.58/4.82  thf('237', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.58/4.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.58/4.82  thf('238', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['236', '237'])).
% 4.58/4.82  thf('239', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 4.58/4.82      inference('demod', [status(thm)], ['0', '66'])).
% 4.58/4.82  thf('240', plain,
% 4.58/4.82      ((~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)
% 4.58/4.82        | ((sk_C_2) = (k1_xboole_0)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['238', '239'])).
% 4.58/4.82  thf('241', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('demod', [status(thm)], ['157', '158'])).
% 4.58/4.82  thf('242', plain, (((sk_C_2) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['240', '241'])).
% 4.58/4.82  thf('243', plain,
% 4.58/4.82      (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D)),
% 4.58/4.82      inference('demod', [status(thm)], ['67', '242'])).
% 4.58/4.82  thf('244', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 4.58/4.82      inference('demod', [status(thm)], ['90', '93'])).
% 4.58/4.82  thf('245', plain, ((((sk_C_2) = (sk_D)) | ~ (v1_xboole_0 @ sk_A))),
% 4.58/4.82      inference('sup-', [status(thm)], ['233', '234'])).
% 4.58/4.82  thf('246', plain,
% 4.58/4.82      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.58/4.82        | ((sk_D) = (k1_xboole_0))
% 4.58/4.82        | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('sup-', [status(thm)], ['244', '245'])).
% 4.58/4.82  thf('247', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.58/4.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.58/4.82  thf('248', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['246', '247'])).
% 4.58/4.82  thf('249', plain, (((sk_C_2) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['240', '241'])).
% 4.58/4.82  thf('250', plain, ((((sk_D) = (k1_xboole_0)) | ((k1_xboole_0) = (sk_D)))),
% 4.58/4.82      inference('demod', [status(thm)], ['248', '249'])).
% 4.58/4.82  thf('251', plain, (((sk_D) = (k1_xboole_0))),
% 4.58/4.82      inference('simplify', [status(thm)], ['250'])).
% 4.58/4.82  thf('252', plain,
% 4.58/4.82      (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.58/4.82      inference('demod', [status(thm)], ['243', '251'])).
% 4.58/4.82  thf('253', plain, ((r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 4.58/4.82      inference('demod', [status(thm)], ['157', '158'])).
% 4.58/4.82  thf('254', plain, (((sk_C_2) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['240', '241'])).
% 4.58/4.82  thf('255', plain, (((sk_C_2) = (k1_xboole_0))),
% 4.58/4.82      inference('demod', [status(thm)], ['240', '241'])).
% 4.58/4.82  thf('256', plain,
% 4.58/4.82      ((r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.58/4.82      inference('demod', [status(thm)], ['253', '254', '255'])).
% 4.58/4.82  thf('257', plain, ($false), inference('demod', [status(thm)], ['252', '256'])).
% 4.58/4.82  
% 4.58/4.82  % SZS output end Refutation
% 4.58/4.82  
% 4.58/4.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
