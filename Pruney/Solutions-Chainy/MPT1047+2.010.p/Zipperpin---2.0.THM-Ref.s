%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CU7cQXC2th

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:22 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  267 (15068 expanded)
%              Number of leaves         :   30 (4010 expanded)
%              Depth                    :   41
%              Number of atoms          : 5294 (352794 expanded)
%              Number of equality atoms :  340 (14326 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t164_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
            = ( k1_tarski @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
              = ( k1_tarski @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t143_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r1_partfun1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ ( k1_tarski @ X28 ) ) ) )
      | ( r1_partfun1 @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ ( k1_tarski @ X28 ) ) ) )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( X9 != X10 )
      | ~ ( v1_partfun1 @ X9 @ X13 )
      | ~ ( r1_partfun1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X8: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( r1_partfun1 @ X8 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_partfun1 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( r1_partfun1 @ X8 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_partfun1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( r1_partfun1 @ X0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('59',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','63'])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X14 )
      | ( zip_tseitin_0 @ ( sk_F @ X14 @ X15 @ X16 @ X17 ) @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X15 @ X16 @ X17 )
      | ( X14
        = ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('75',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('82',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X33 = X30 )
      | ~ ( r1_partfun1 @ X33 @ X30 )
      | ~ ( v1_partfun1 @ X30 @ X31 )
      | ~ ( v1_partfun1 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
      | ~ ( r1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D )
      | ~ ( r1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( r1_partfun1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D )
      | ~ ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['72','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('101',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X34 @ X35 )
      | ( ( k5_partfun1 @ X35 @ X36 @ X34 )
        = ( k1_tarski @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('119',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('120',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( v1_funct_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('124',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('125',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('126',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( v1_partfun1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('130',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('131',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('132',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( m1_subset_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('137',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,
    ( ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('142',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ~ ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['139','143'])).

thf('145',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['128','145'])).

thf('147',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['122','147'])).

thf('149',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('151',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('154',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('158',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('160',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('161',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_funct_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['158','161'])).

thf('163',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('165',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('166',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('167',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_partfun1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('171',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('172',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('173',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('174',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['171','174'])).

thf('176',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('178',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','178'])).

thf('180',plain,
    ( ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('183',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ~ ( r1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['180','184'])).

thf('186',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['169','186'])).

thf('188',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['163','188'])).

thf('190',plain,
    ( ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( ( sk_F @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
     != sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(eq_fact,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(clc,[status(thm)],['149','191'])).

thf('193',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference(clc,[status(thm)],['149','191'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X14 )
      | ~ ( zip_tseitin_0 @ X18 @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X15 @ X16 @ X17 )
      | ( X14
        = ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_D )
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','198'])).

thf('200',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('205',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('207',plain,
    ( ( r1_partfun1 @ sk_D @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    r1_partfun1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('211',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X15: $i,X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['211','216'])).

thf('218',plain,
    ( ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['204','217'])).

thf('219',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['203','219'])).

thf('221',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','220'])).

thf('222',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['221'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('223',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('225',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('226',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['224','226'])).

thf('228',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['227'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['221'])).

thf('233',plain,(
    ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( X0
     != ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['230','233'])).

thf('235',plain,(
    $false ),
    inference(simplify,[status(thm)],['234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CU7cQXC2th
% 0.14/0.37  % Computer   : n007.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:05:51 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 2.22/2.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.22/2.40  % Solved by: fo/fo7.sh
% 2.22/2.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.40  % done 3432 iterations in 1.907s
% 2.22/2.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.22/2.40  % SZS output start Refutation
% 2.22/2.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.22/2.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.22/2.40  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 2.22/2.40  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 2.22/2.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.22/2.40  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 2.22/2.40  thf(sk_C_type, type, sk_C: $i).
% 2.22/2.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.22/2.40  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.22/2.40  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 2.22/2.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.22/2.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.22/2.40  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.22/2.40  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.40  thf(sk_D_type, type, sk_D: $i).
% 2.22/2.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.22/2.40  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 2.22/2.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.22/2.40  thf(t164_funct_2, conjecture,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.40         ( m1_subset_1 @
% 2.22/2.40           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 2.22/2.40       ( ![D:$i]:
% 2.22/2.40         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 2.22/2.40             ( m1_subset_1 @
% 2.22/2.40               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 2.22/2.40           ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ))).
% 2.22/2.40  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.40    (~( ![A:$i,B:$i,C:$i]:
% 2.22/2.40        ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.40            ( m1_subset_1 @
% 2.22/2.40              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 2.22/2.40          ( ![D:$i]:
% 2.22/2.40            ( ( ( v1_funct_1 @ D ) & 
% 2.22/2.40                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 2.22/2.40                ( m1_subset_1 @
% 2.22/2.40                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 2.22/2.40              ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ) )),
% 2.22/2.40    inference('cnf.neg', [status(esa)], [t164_funct_2])).
% 2.22/2.40  thf('0', plain,
% 2.22/2.40      ((m1_subset_1 @ sk_C @ 
% 2.22/2.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('1', plain,
% 2.22/2.40      ((m1_subset_1 @ sk_D @ 
% 2.22/2.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf(t143_partfun1, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.40         ( m1_subset_1 @
% 2.22/2.40           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 2.22/2.40       ( ![D:$i]:
% 2.22/2.40         ( ( ( v1_funct_1 @ D ) & 
% 2.22/2.40             ( m1_subset_1 @
% 2.22/2.40               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 2.22/2.40           ( r1_partfun1 @ C @ D ) ) ) ))).
% 2.22/2.40  thf('2', plain,
% 2.22/2.40      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.22/2.40         (~ (v1_funct_1 @ X26)
% 2.22/2.40          | ~ (m1_subset_1 @ X26 @ 
% 2.22/2.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ (k1_tarski @ X28))))
% 2.22/2.40          | (r1_partfun1 @ X29 @ X26)
% 2.22/2.40          | ~ (m1_subset_1 @ X29 @ 
% 2.22/2.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ (k1_tarski @ X28))))
% 2.22/2.40          | ~ (v1_funct_1 @ X29))),
% 2.22/2.40      inference('cnf', [status(esa)], [t143_partfun1])).
% 2.22/2.40  thf('3', plain,
% 2.22/2.40      (![X0 : $i]:
% 2.22/2.40         (~ (v1_funct_1 @ X0)
% 2.22/2.40          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.40          | (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.40          | ~ (v1_funct_1 @ sk_D))),
% 2.22/2.40      inference('sup-', [status(thm)], ['1', '2'])).
% 2.22/2.40  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('5', plain,
% 2.22/2.40      (![X0 : $i]:
% 2.22/2.40         (~ (v1_funct_1 @ X0)
% 2.22/2.40          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.40          | (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.40      inference('demod', [status(thm)], ['3', '4'])).
% 2.22/2.40  thf('6', plain, (((r1_partfun1 @ sk_C @ sk_D) | ~ (v1_funct_1 @ sk_C))),
% 2.22/2.40      inference('sup-', [status(thm)], ['0', '5'])).
% 2.22/2.40  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('8', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 2.22/2.40      inference('demod', [status(thm)], ['6', '7'])).
% 2.22/2.40  thf('9', plain,
% 2.22/2.40      ((m1_subset_1 @ sk_D @ 
% 2.22/2.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf(t132_funct_2, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.40       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.40           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.40         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.22/2.40           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.22/2.40  thf('10', plain,
% 2.22/2.40      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.22/2.40         (((X23) = (k1_xboole_0))
% 2.22/2.40          | ~ (v1_funct_1 @ X24)
% 2.22/2.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 2.22/2.40          | (v1_partfun1 @ X24 @ X25)
% 2.22/2.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 2.22/2.40          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 2.22/2.40          | ~ (v1_funct_1 @ X24))),
% 2.22/2.40      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.22/2.40  thf('11', plain,
% 2.22/2.40      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.22/2.40         (~ (v1_funct_2 @ X24 @ X25 @ X23)
% 2.22/2.40          | (v1_partfun1 @ X24 @ X25)
% 2.22/2.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 2.22/2.40          | ~ (v1_funct_1 @ X24)
% 2.22/2.40          | ((X23) = (k1_xboole_0)))),
% 2.22/2.40      inference('simplify', [status(thm)], ['10'])).
% 2.22/2.40  thf('12', plain,
% 2.22/2.40      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.40        | ~ (v1_funct_1 @ sk_D)
% 2.22/2.40        | (v1_partfun1 @ sk_D @ sk_A)
% 2.22/2.40        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 2.22/2.40      inference('sup-', [status(thm)], ['9', '11'])).
% 2.22/2.40  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('15', plain,
% 2.22/2.40      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 2.22/2.40      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.22/2.40  thf('16', plain,
% 2.22/2.40      ((m1_subset_1 @ sk_D @ 
% 2.22/2.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf(d7_partfun1, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.22/2.40         ( v1_funct_1 @ C ) ) =>
% 2.22/2.40       ( ![D:$i]:
% 2.22/2.40         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 2.22/2.40           ( ![E:$i]:
% 2.22/2.40             ( ( r2_hidden @ E @ D ) <=>
% 2.22/2.40               ( ?[F:$i]:
% 2.22/2.40                 ( ( v1_funct_1 @ F ) & 
% 2.22/2.40                   ( m1_subset_1 @
% 2.22/2.40                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.22/2.40                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 2.22/2.40                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 2.22/2.40  thf(zf_stmt_1, axiom,
% 2.22/2.40    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 2.22/2.40     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 2.22/2.40       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 2.22/2.41         ( ( F ) = ( E ) ) & 
% 2.22/2.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.22/2.41         ( v1_funct_1 @ F ) ) ))).
% 2.22/2.41  thf('17', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13)
% 2.22/2.41          | ~ (v1_funct_1 @ X9)
% 2.22/2.41          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 2.22/2.41          | ((X9) != (X10))
% 2.22/2.41          | ~ (v1_partfun1 @ X9 @ X13)
% 2.22/2.41          | ~ (r1_partfun1 @ X8 @ X9))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('18', plain,
% 2.22/2.41      (![X8 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 2.22/2.41         (~ (r1_partfun1 @ X8 @ X10)
% 2.22/2.41          | ~ (v1_partfun1 @ X10 @ X13)
% 2.22/2.41          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 2.22/2.41          | ~ (v1_funct_1 @ X10)
% 2.22/2.41          | (zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13))),
% 2.22/2.41      inference('simplify', [status(thm)], ['17'])).
% 2.22/2.41  thf('19', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (v1_funct_1 @ sk_D)
% 2.22/2.41          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.41      inference('sup-', [status(thm)], ['16', '18'])).
% 2.22/2.41  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('21', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.41      inference('demod', [status(thm)], ['19', '20'])).
% 2.22/2.41  thf('22', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['15', '21'])).
% 2.22/2.41  thf('23', plain,
% 2.22/2.41      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['8', '22'])).
% 2.22/2.41  thf('24', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_C @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.22/2.41  thf(zf_stmt_3, axiom,
% 2.22/2.41    (![A:$i,B:$i,C:$i]:
% 2.22/2.41     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.41       ( ![D:$i]:
% 2.22/2.41         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 2.22/2.41           ( ![E:$i]:
% 2.22/2.41             ( ( r2_hidden @ E @ D ) <=>
% 2.22/2.41               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 2.22/2.41  thf('25', plain,
% 2.22/2.41      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 2.22/2.41         (((X19) != (k5_partfun1 @ X17 @ X16 @ X15))
% 2.22/2.41          | (r2_hidden @ X21 @ X19)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (v1_funct_1 @ X15))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.41  thf('26', plain,
% 2.22/2.41      (![X15 : $i, X16 : $i, X17 : $i, X21 : $i, X22 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X15)
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 2.22/2.41          | (r2_hidden @ X21 @ (k5_partfun1 @ X17 @ X16 @ X15)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['25'])).
% 2.22/2.41  thf('27', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (v1_funct_1 @ sk_C))),
% 2.22/2.41      inference('sup-', [status(thm)], ['24', '26'])).
% 2.22/2.41  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('29', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('demod', [status(thm)], ['27', '28'])).
% 2.22/2.41  thf('30', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['23', '29'])).
% 2.22/2.41  thf('31', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_C @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('32', plain,
% 2.22/2.41      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 2.22/2.41         (((X19) != (k5_partfun1 @ X17 @ X16 @ X15))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 2.22/2.41             X16 @ X17)
% 2.22/2.41          | ~ (r2_hidden @ X20 @ X19)
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (v1_funct_1 @ X15))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.41  thf('33', plain,
% 2.22/2.41      (![X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X15)
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (r2_hidden @ X20 @ (k5_partfun1 @ X17 @ X16 @ X15))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 2.22/2.41             X16 @ X17))),
% 2.22/2.41      inference('simplify', [status(thm)], ['32'])).
% 2.22/2.41  thf('34', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ X0 @ 
% 2.22/2.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ~ (v1_funct_1 @ sk_C))),
% 2.22/2.41      inference('sup-', [status(thm)], ['31', '33'])).
% 2.22/2.41  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('36', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ X0 @ 
% 2.22/2.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('demod', [status(thm)], ['34', '35'])).
% 2.22/2.41  thf('37', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['30', '36'])).
% 2.22/2.41  thf('38', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('39', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['37', '38'])).
% 2.22/2.41  thf('40', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['30', '36'])).
% 2.22/2.41  thf('41', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((r1_partfun1 @ X8 @ X9)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('42', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r1_partfun1 @ sk_C @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['40', '41'])).
% 2.22/2.41  thf('43', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['30', '36'])).
% 2.22/2.41  thf('44', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('45', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (v1_funct_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['43', '44'])).
% 2.22/2.41  thf('46', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['30', '36'])).
% 2.22/2.41  thf('47', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_partfun1 @ X9 @ X12)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('48', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (v1_partfun1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['46', '47'])).
% 2.22/2.41  thf('49', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['30', '36'])).
% 2.22/2.41  thf('50', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('51', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (m1_subset_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('sup-', [status(thm)], ['49', '50'])).
% 2.22/2.41  thf('52', plain,
% 2.22/2.41      (![X8 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 2.22/2.41         (~ (r1_partfun1 @ X8 @ X10)
% 2.22/2.41          | ~ (v1_partfun1 @ X10 @ X13)
% 2.22/2.41          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 2.22/2.41          | ~ (v1_funct_1 @ X10)
% 2.22/2.41          | (zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13))),
% 2.22/2.41      inference('simplify', [status(thm)], ['17'])).
% 2.22/2.41  thf('53', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | (zip_tseitin_0 @ 
% 2.22/2.41             (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ~ (v1_partfun1 @ 
% 2.22/2.41               (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ 
% 2.22/2.41               (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['51', '52'])).
% 2.22/2.41  thf('54', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ 
% 2.22/2.41               (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | (zip_tseitin_0 @ 
% 2.22/2.41             (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['48', '53'])).
% 2.22/2.41  thf('55', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ 
% 2.22/2.41               (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['54'])).
% 2.22/2.41  thf('56', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ 
% 2.22/2.41               (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | (zip_tseitin_0 @ 
% 2.22/2.41             (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['45', '55'])).
% 2.22/2.41  thf('57', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ 
% 2.22/2.41               (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['56'])).
% 2.22/2.41  thf('58', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['42', '57'])).
% 2.22/2.41  thf('59', plain,
% 2.22/2.41      (((zip_tseitin_0 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41         (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['58'])).
% 2.22/2.41  thf('60', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('demod', [status(thm)], ['27', '28'])).
% 2.22/2.41  thf('61', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r2_hidden @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['59', '60'])).
% 2.22/2.41  thf('62', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ X0 @ 
% 2.22/2.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('demod', [status(thm)], ['34', '35'])).
% 2.22/2.41  thf('63', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41           (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['61', '62'])).
% 2.22/2.41  thf('64', plain,
% 2.22/2.41      (((zip_tseitin_0 @ 
% 2.22/2.41         (sk_F_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41          (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['39', '63'])).
% 2.22/2.41  thf('65', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('simplify', [status(thm)], ['64'])).
% 2.22/2.41  thf('66', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_C @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('67', plain,
% 2.22/2.41      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X14 @ X15 @ X16 @ X17) @ X14)
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F @ X14 @ X15 @ X16 @ X17) @ 
% 2.22/2.41             (sk_E @ X14 @ X15 @ X16 @ X17) @ X15 @ X16 @ X17)
% 2.22/2.41          | ((X14) = (k5_partfun1 @ X17 @ X16 @ X15))
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (v1_funct_1 @ X15))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.41  thf('68', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ sk_C)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('sup-', [status(thm)], ['66', '67'])).
% 2.22/2.41  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('70', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('demod', [status(thm)], ['68', '69'])).
% 2.22/2.41  thf('71', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('72', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['70', '71'])).
% 2.22/2.41  thf('73', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['70', '71'])).
% 2.22/2.41  thf('74', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('demod', [status(thm)], ['68', '69'])).
% 2.22/2.41  thf('75', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('76', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (m1_subset_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('sup-', [status(thm)], ['74', '75'])).
% 2.22/2.41  thf('77', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X0)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.41      inference('demod', [status(thm)], ['3', '4'])).
% 2.22/2.41  thf('78', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | (r1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_D)
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['76', '77'])).
% 2.22/2.41  thf('79', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | (r1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_D)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['73', '78'])).
% 2.22/2.41  thf('80', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['79'])).
% 2.22/2.41  thf('81', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('demod', [status(thm)], ['68', '69'])).
% 2.22/2.41  thf('82', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_partfun1 @ X9 @ X12)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('83', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (v1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['81', '82'])).
% 2.22/2.41  thf('84', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (m1_subset_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('sup-', [status(thm)], ['74', '75'])).
% 2.22/2.41  thf('85', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 2.22/2.41      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.22/2.41  thf('86', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_D @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf(t148_partfun1, axiom,
% 2.22/2.41    (![A:$i,B:$i,C:$i]:
% 2.22/2.41     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.41       ( ![D:$i]:
% 2.22/2.41         ( ( ( v1_funct_1 @ D ) & 
% 2.22/2.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.41           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 2.22/2.41               ( r1_partfun1 @ C @ D ) ) =>
% 2.22/2.41             ( ( C ) = ( D ) ) ) ) ) ))).
% 2.22/2.41  thf('87', plain,
% 2.22/2.41      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X30)
% 2.22/2.41          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.22/2.41          | ((X33) = (X30))
% 2.22/2.41          | ~ (r1_partfun1 @ X33 @ X30)
% 2.22/2.41          | ~ (v1_partfun1 @ X30 @ X31)
% 2.22/2.41          | ~ (v1_partfun1 @ X33 @ X31)
% 2.22/2.41          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.22/2.41          | ~ (v1_funct_1 @ X33))),
% 2.22/2.41      inference('cnf', [status(esa)], [t148_partfun1])).
% 2.22/2.41  thf('88', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X0)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | ~ (v1_partfun1 @ X0 @ sk_A)
% 2.22/2.41          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | ((X0) = (sk_D))
% 2.22/2.41          | ~ (v1_funct_1 @ sk_D))),
% 2.22/2.41      inference('sup-', [status(thm)], ['86', '87'])).
% 2.22/2.41  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('90', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X0)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | ~ (v1_partfun1 @ X0 @ sk_A)
% 2.22/2.41          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | ((X0) = (sk_D)))),
% 2.22/2.41      inference('demod', [status(thm)], ['88', '89'])).
% 2.22/2.41  thf('91', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((X0) = (sk_D))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | ~ (v1_partfun1 @ X0 @ sk_A)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | ~ (v1_funct_1 @ X0))),
% 2.22/2.41      inference('sup-', [status(thm)], ['85', '90'])).
% 2.22/2.41  thf('92', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ~ (v1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41               sk_A)
% 2.22/2.41          | ~ (r1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41               sk_D)
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['84', '91'])).
% 2.22/2.41  thf('93', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D))
% 2.22/2.41          | ~ (r1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41               sk_D)
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['83', '92'])).
% 2.22/2.41  thf('94', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ~ (r1_partfun1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41               sk_D)
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['93'])).
% 2.22/2.41  thf('95', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D))
% 2.22/2.41          | ~ (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['80', '94'])).
% 2.22/2.41  thf('96', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['95'])).
% 2.22/2.41  thf('97', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['72', '96'])).
% 2.22/2.41  thf('98', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['97'])).
% 2.22/2.41  thf('99', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 2.22/2.41      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.22/2.41  thf('100', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_D @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf(t174_partfun1, axiom,
% 2.22/2.41    (![A:$i,B:$i,C:$i]:
% 2.22/2.41     ( ( ( v1_funct_1 @ C ) & 
% 2.22/2.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.41       ( ( v1_partfun1 @ C @ A ) <=>
% 2.22/2.41         ( ( k5_partfun1 @ A @ B @ C ) = ( k1_tarski @ C ) ) ) ))).
% 2.22/2.41  thf('101', plain,
% 2.22/2.41      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.22/2.41         (~ (v1_partfun1 @ X34 @ X35)
% 2.22/2.41          | ((k5_partfun1 @ X35 @ X36 @ X34) = (k1_tarski @ X34))
% 2.22/2.41          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.22/2.41          | ~ (v1_funct_1 @ X34))),
% 2.22/2.41      inference('cnf', [status(esa)], [t174_partfun1])).
% 2.22/2.41  thf('102', plain,
% 2.22/2.41      ((~ (v1_funct_1 @ sk_D)
% 2.22/2.41        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)
% 2.22/2.41            = (k1_tarski @ sk_D))
% 2.22/2.41        | ~ (v1_partfun1 @ sk_D @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['100', '101'])).
% 2.22/2.41  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('104', plain,
% 2.22/2.41      ((((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 2.22/2.41        | ~ (v1_partfun1 @ sk_D @ sk_A))),
% 2.22/2.41      inference('demod', [status(thm)], ['102', '103'])).
% 2.22/2.41  thf('105', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)
% 2.22/2.41            = (k1_tarski @ sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['99', '104'])).
% 2.22/2.41  thf('106', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_D @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('107', plain,
% 2.22/2.41      (![X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X15)
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (r2_hidden @ X20 @ (k5_partfun1 @ X17 @ X16 @ X15))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 2.22/2.41             X16 @ X17))),
% 2.22/2.41      inference('simplify', [status(thm)], ['32'])).
% 2.22/2.41  thf('108', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ X0 @ 
% 2.22/2.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D))
% 2.22/2.41          | ~ (v1_funct_1 @ sk_D))),
% 2.22/2.41      inference('sup-', [status(thm)], ['106', '107'])).
% 2.22/2.41  thf('109', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('110', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ X0 @ 
% 2.22/2.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 2.22/2.41      inference('demod', [status(thm)], ['108', '109'])).
% 2.22/2.41  thf('111', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | (zip_tseitin_0 @ 
% 2.22/2.41             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['105', '110'])).
% 2.22/2.41  thf('112', plain,
% 2.22/2.41      ((((k1_tarski @ sk_D) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['98', '111'])).
% 2.22/2.41  thf('113', plain,
% 2.22/2.41      (((zip_tseitin_0 @ 
% 2.22/2.41         (sk_F_1 @ 
% 2.22/2.41          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k1_tarski @ sk_D)
% 2.22/2.41            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['112'])).
% 2.22/2.41  thf('114', plain,
% 2.22/2.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('115', plain,
% 2.22/2.41      (((zip_tseitin_0 @ 
% 2.22/2.41         (sk_F_1 @ 
% 2.22/2.41          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 2.22/2.41  thf('116', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('117', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['115', '116'])).
% 2.22/2.41  thf('118', plain,
% 2.22/2.41      (((zip_tseitin_0 @ 
% 2.22/2.41         (sk_F_1 @ 
% 2.22/2.41          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 2.22/2.41  thf('119', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('120', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (v1_funct_1 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['118', '119'])).
% 2.22/2.41  thf('121', plain,
% 2.22/2.41      (((v1_funct_1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['117', '120'])).
% 2.22/2.41  thf('122', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (v1_funct_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['121'])).
% 2.22/2.41  thf('123', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['115', '116'])).
% 2.22/2.41  thf('124', plain,
% 2.22/2.41      (((zip_tseitin_0 @ 
% 2.22/2.41         (sk_F_1 @ 
% 2.22/2.41          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 2.22/2.41  thf('125', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_partfun1 @ X9 @ X12)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('126', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (v1_partfun1 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['124', '125'])).
% 2.22/2.41  thf('127', plain,
% 2.22/2.41      (((v1_partfun1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['123', '126'])).
% 2.22/2.41  thf('128', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (v1_partfun1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_A))),
% 2.22/2.41      inference('simplify', [status(thm)], ['127'])).
% 2.22/2.41  thf('129', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (v1_funct_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['121'])).
% 2.22/2.41  thf('130', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['115', '116'])).
% 2.22/2.41  thf('131', plain,
% 2.22/2.41      (((zip_tseitin_0 @ 
% 2.22/2.41         (sk_F_1 @ 
% 2.22/2.41          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 2.22/2.41  thf('132', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('133', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (m1_subset_1 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('sup-', [status(thm)], ['131', '132'])).
% 2.22/2.41  thf('134', plain,
% 2.22/2.41      (((m1_subset_1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['130', '133'])).
% 2.22/2.41  thf('135', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (m1_subset_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('simplify', [status(thm)], ['134'])).
% 2.22/2.41  thf('136', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X0)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.41      inference('demod', [status(thm)], ['3', '4'])).
% 2.22/2.41  thf('137', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r1_partfun1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D)
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['135', '136'])).
% 2.22/2.41  thf('138', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r1_partfun1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['129', '137'])).
% 2.22/2.41  thf('139', plain,
% 2.22/2.41      (((r1_partfun1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['138'])).
% 2.22/2.41  thf('140', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | (m1_subset_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('simplify', [status(thm)], ['134'])).
% 2.22/2.41  thf('141', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((X0) = (sk_D))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | ~ (v1_partfun1 @ X0 @ sk_A)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | ~ (v1_funct_1 @ X0))),
% 2.22/2.41      inference('sup-', [status(thm)], ['85', '90'])).
% 2.22/2.41  thf('142', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ~ (r1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_D)
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['140', '141'])).
% 2.22/2.41  thf('143', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ~ (r1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_D)
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['142'])).
% 2.22/2.41  thf('144', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['139', '143'])).
% 2.22/2.41  thf('145', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['144'])).
% 2.22/2.41  thf('146', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['128', '145'])).
% 2.22/2.41  thf('147', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['146'])).
% 2.22/2.41  thf('148', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['122', '147'])).
% 2.22/2.41  thf('149', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['148'])).
% 2.22/2.41  thf('150', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('demod', [status(thm)], ['68', '69'])).
% 2.22/2.41  thf('151', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('152', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ((sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41              = (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['150', '151'])).
% 2.22/2.41  thf('153', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | (zip_tseitin_0 @ 
% 2.22/2.41             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 2.22/2.41             (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['105', '110'])).
% 2.22/2.41  thf('154', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_D)
% 2.22/2.41            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['152', '153'])).
% 2.22/2.41  thf('155', plain,
% 2.22/2.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('156', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 2.22/2.41  thf('157', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('158', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['156', '157'])).
% 2.22/2.41  thf('159', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 2.22/2.41  thf('160', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('161', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (v1_funct_1 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['159', '160'])).
% 2.22/2.41  thf('162', plain,
% 2.22/2.41      (((v1_funct_1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['158', '161'])).
% 2.22/2.41  thf('163', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (v1_funct_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['162'])).
% 2.22/2.41  thf('164', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['156', '157'])).
% 2.22/2.41  thf('165', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 2.22/2.41  thf('166', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((v1_partfun1 @ X9 @ X12)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('167', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (v1_partfun1 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['165', '166'])).
% 2.22/2.41  thf('168', plain,
% 2.22/2.41      (((v1_partfun1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['164', '167'])).
% 2.22/2.41  thf('169', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (v1_partfun1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_A))),
% 2.22/2.41      inference('simplify', [status(thm)], ['168'])).
% 2.22/2.41  thf('170', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (v1_funct_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['162'])).
% 2.22/2.41  thf('171', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['156', '157'])).
% 2.22/2.41  thf('172', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (zip_tseitin_0 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 2.22/2.41  thf('173', plain,
% 2.22/2.41      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.22/2.41         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.41  thf('174', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (m1_subset_1 @ 
% 2.22/2.41           (sk_F_1 @ 
% 2.22/2.41            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('sup-', [status(thm)], ['172', '173'])).
% 2.22/2.41  thf('175', plain,
% 2.22/2.41      (((m1_subset_1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['171', '174'])).
% 2.22/2.41  thf('176', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (m1_subset_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('simplify', [status(thm)], ['175'])).
% 2.22/2.41  thf('177', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X0)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.41      inference('demod', [status(thm)], ['3', '4'])).
% 2.22/2.41  thf('178', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r1_partfun1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D)
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['176', '177'])).
% 2.22/2.41  thf('179', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r1_partfun1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           sk_D)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['170', '178'])).
% 2.22/2.41  thf('180', plain,
% 2.22/2.41      (((r1_partfun1 @ 
% 2.22/2.41         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['179'])).
% 2.22/2.41  thf('181', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | (m1_subset_1 @ 
% 2.22/2.41           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 2.22/2.41      inference('simplify', [status(thm)], ['175'])).
% 2.22/2.41  thf('182', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((X0) = (sk_D))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | ~ (v1_partfun1 @ X0 @ sk_A)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | ~ (v1_funct_1 @ X0))),
% 2.22/2.41      inference('sup-', [status(thm)], ['85', '90'])).
% 2.22/2.41  thf('183', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ~ (r1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_D)
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['181', '182'])).
% 2.22/2.41  thf('184', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ~ (r1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_D)
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['183'])).
% 2.22/2.41  thf('185', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['180', '184'])).
% 2.22/2.41  thf('186', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ~ (v1_partfun1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41             sk_A)
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['185'])).
% 2.22/2.41  thf('187', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['169', '186'])).
% 2.22/2.41  thf('188', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ~ (v1_funct_1 @ 
% 2.22/2.41             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['187'])).
% 2.22/2.41  thf('189', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['163', '188'])).
% 2.22/2.41  thf('190', plain,
% 2.22/2.41      ((((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          = (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['189'])).
% 2.22/2.41  thf('191', plain,
% 2.22/2.41      ((((sk_F @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          != (sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('eq_fact', [status(thm)], ['190'])).
% 2.22/2.41  thf('192', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('clc', [status(thm)], ['149', '191'])).
% 2.22/2.41  thf('193', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41            = (sk_D)))),
% 2.22/2.41      inference('clc', [status(thm)], ['149', '191'])).
% 2.22/2.41  thf('194', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_C @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('195', plain,
% 2.22/2.41      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.22/2.41         (~ (r2_hidden @ (sk_E @ X14 @ X15 @ X16 @ X17) @ X14)
% 2.22/2.41          | ~ (zip_tseitin_0 @ X18 @ (sk_E @ X14 @ X15 @ X16 @ X17) @ X15 @ 
% 2.22/2.41               X16 @ X17)
% 2.22/2.41          | ((X14) = (k5_partfun1 @ X17 @ X16 @ X15))
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (v1_funct_1 @ X15))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.41  thf('196', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ sk_C)
% 2.22/2.41          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ 
% 2.22/2.41               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41               (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('sup-', [status(thm)], ['194', '195'])).
% 2.22/2.41  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('198', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ 
% 2.22/2.41               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 2.22/2.41               (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 2.22/2.41      inference('demod', [status(thm)], ['196', '197'])).
% 2.22/2.41  thf('199', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r2_hidden @ 
% 2.22/2.41               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41               (k1_tarski @ sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_D)
% 2.22/2.41              = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['193', '198'])).
% 2.22/2.41  thf('200', plain,
% 2.22/2.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('201', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r2_hidden @ 
% 2.22/2.41               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 2.22/2.41               (k1_tarski @ sk_D)))),
% 2.22/2.41      inference('simplify_reflect-', [status(thm)], ['199', '200'])).
% 2.22/2.41  thf('202', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['192', '201'])).
% 2.22/2.41  thf('203', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['202'])).
% 2.22/2.41  thf('204', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)
% 2.22/2.41            = (k1_tarski @ sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['99', '104'])).
% 2.22/2.41  thf('205', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_D @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('206', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X0)
% 2.22/2.41          | ~ (m1_subset_1 @ X0 @ 
% 2.22/2.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 2.22/2.41          | (r1_partfun1 @ X0 @ sk_D))),
% 2.22/2.41      inference('demod', [status(thm)], ['3', '4'])).
% 2.22/2.41  thf('207', plain, (((r1_partfun1 @ sk_D @ sk_D) | ~ (v1_funct_1 @ sk_D))),
% 2.22/2.41      inference('sup-', [status(thm)], ['205', '206'])).
% 2.22/2.41  thf('208', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('209', plain, ((r1_partfun1 @ sk_D @ sk_D)),
% 2.22/2.41      inference('demod', [status(thm)], ['207', '208'])).
% 2.22/2.41  thf('210', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.22/2.41          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('sup-', [status(thm)], ['15', '21'])).
% 2.22/2.41  thf('211', plain,
% 2.22/2.41      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['209', '210'])).
% 2.22/2.41  thf('212', plain,
% 2.22/2.41      ((m1_subset_1 @ sk_D @ 
% 2.22/2.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('213', plain,
% 2.22/2.41      (![X15 : $i, X16 : $i, X17 : $i, X21 : $i, X22 : $i]:
% 2.22/2.41         (~ (v1_funct_1 @ X15)
% 2.22/2.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 2.22/2.41          | (r2_hidden @ X21 @ (k5_partfun1 @ X17 @ X16 @ X15)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['25'])).
% 2.22/2.41  thf('214', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 2.22/2.41          | ~ (v1_funct_1 @ sk_D))),
% 2.22/2.41      inference('sup-', [status(thm)], ['212', '213'])).
% 2.22/2.41  thf('215', plain, ((v1_funct_1 @ sk_D)),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('216', plain,
% 2.22/2.41      (![X0 : $i, X1 : $i]:
% 2.22/2.41         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('demod', [status(thm)], ['214', '215'])).
% 2.22/2.41  thf('217', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['211', '216'])).
% 2.22/2.41  thf('218', plain,
% 2.22/2.41      (((r2_hidden @ sk_D @ (k1_tarski @ sk_D))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup+', [status(thm)], ['204', '217'])).
% 2.22/2.41  thf('219', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))),
% 2.22/2.41      inference('simplify', [status(thm)], ['218'])).
% 2.22/2.41  thf('220', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 2.22/2.41      inference('clc', [status(thm)], ['203', '219'])).
% 2.22/2.41  thf('221', plain,
% 2.22/2.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 2.22/2.41        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['65', '220'])).
% 2.22/2.41  thf('222', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 2.22/2.41      inference('simplify', [status(thm)], ['221'])).
% 2.22/2.41  thf(t130_zfmisc_1, axiom,
% 2.22/2.41    (![A:$i,B:$i]:
% 2.22/2.41     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 2.22/2.41       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 2.22/2.41         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 2.22/2.41  thf('223', plain,
% 2.22/2.41      (![X6 : $i, X7 : $i]:
% 2.22/2.41         (((X6) = (k1_xboole_0))
% 2.22/2.41          | ((k2_zfmisc_1 @ (k1_tarski @ X7) @ X6) != (k1_xboole_0)))),
% 2.22/2.41      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 2.22/2.41  thf('224', plain,
% 2.22/2.41      (![X0 : $i]:
% 2.22/2.41         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 2.22/2.41          | ((X0) = (k1_xboole_0)))),
% 2.22/2.41      inference('sup-', [status(thm)], ['222', '223'])).
% 2.22/2.41  thf(t113_zfmisc_1, axiom,
% 2.22/2.41    (![A:$i,B:$i]:
% 2.22/2.41     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.22/2.41       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.22/2.41  thf('225', plain,
% 2.22/2.41      (![X4 : $i, X5 : $i]:
% 2.22/2.41         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.22/2.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.22/2.41  thf('226', plain,
% 2.22/2.41      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.41      inference('simplify', [status(thm)], ['225'])).
% 2.22/2.41  thf('227', plain,
% 2.22/2.41      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 2.22/2.41      inference('demod', [status(thm)], ['224', '226'])).
% 2.22/2.41  thf('228', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 2.22/2.41      inference('simplify', [status(thm)], ['227'])).
% 2.22/2.41  thf('229', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 2.22/2.41      inference('simplify', [status(thm)], ['227'])).
% 2.22/2.41  thf('230', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 2.22/2.41      inference('sup+', [status(thm)], ['228', '229'])).
% 2.22/2.41  thf('231', plain,
% 2.22/2.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 2.22/2.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.41  thf('232', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 2.22/2.41      inference('simplify', [status(thm)], ['221'])).
% 2.22/2.41  thf('233', plain,
% 2.22/2.41      (((k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C) != (k1_tarski @ sk_D))),
% 2.22/2.41      inference('demod', [status(thm)], ['231', '232'])).
% 2.22/2.41  thf('234', plain, (![X0 : $i]: ((X0) != (k1_tarski @ sk_D))),
% 2.22/2.41      inference('sup-', [status(thm)], ['230', '233'])).
% 2.22/2.41  thf('235', plain, ($false), inference('simplify', [status(thm)], ['234'])).
% 2.22/2.41  
% 2.22/2.41  % SZS output end Refutation
% 2.22/2.41  
% 2.22/2.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
