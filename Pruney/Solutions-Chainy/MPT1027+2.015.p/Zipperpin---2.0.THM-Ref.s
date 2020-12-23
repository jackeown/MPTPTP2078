%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XcBdWVkUBU

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:57 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 552 expanded)
%              Number of leaves         :   45 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  979 (6912 expanded)
%              Number of equality atoms :   80 ( 385 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('2',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['9','13'])).

thf('15',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','15','16'])).

thf('18',plain,(
    ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['9','13'])).

thf('19',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('20',plain,(
    ~ ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['24','25'])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ k1_xboole_0 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( sk_F @ X26 @ X27 @ X28 ) @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_F @ sk_B @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_F @ k1_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ X15 @ ( k2_tarski @ X14 @ X16 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X15 @ X14 ) @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X1 ) )
        = ( k2_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('55',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('61',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X11: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','61','62','63'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_tarski @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['50','78'])).

thf('80',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('82',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','79'])).

thf('83',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('84',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('85',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('87',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('88',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('90',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('91',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','88','89','90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('93',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['37','80','81','82','97'])).

thf('99',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('100',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('101',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['21','98','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XcBdWVkUBU
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:52:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 521 iterations in 0.520s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.97  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.97  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.97  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(t130_funct_2, conjecture,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.97       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.75/0.97         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.97           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.97        ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.97          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.75/0.97            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.97              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.75/0.97  thf('0', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(d1_funct_2, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.97       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.97           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.97             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.97         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.97           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.97             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.97  thf(zf_stmt_2, axiom,
% 0.75/0.97    (![C:$i,B:$i,A:$i]:
% 0.75/0.97     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.97       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.97  thf(zf_stmt_4, axiom,
% 0.75/0.97    (![B:$i,A:$i]:
% 0.75/0.97     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.97       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.97  thf(zf_stmt_5, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.97       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.97         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.97           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.97             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.75/0.97         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.75/0.97          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.75/0.97          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.75/0.97        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.97  thf('3', plain,
% 0.75/0.97      (![X30 : $i, X31 : $i]:
% 0.75/0.97         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.97  thf('4', plain,
% 0.75/0.97      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.75/0.97        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.75/0.97  thf('6', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('7', plain,
% 0.75/0.97      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.97         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 0.75/0.97          | (v1_funct_2 @ X34 @ X32 @ X33)
% 0.75/0.97          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      ((((sk_A) != (sk_A))
% 0.75/0.97        | ~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.75/0.97        | (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.97  thf('9', plain,
% 0.75/0.97      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.75/0.97        | ~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.75/0.97      inference('simplify', [status(thm)], ['8'])).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      ((~ (v1_funct_1 @ sk_C_1)
% 0.75/0.97        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.75/0.97        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('12', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('13', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.75/0.97      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.75/0.97  thf('14', plain, (~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.97      inference('clc', [status(thm)], ['9', '13'])).
% 0.75/0.97  thf('15', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.97  thf('16', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.97  thf('17', plain,
% 0.75/0.97      (((zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A)
% 0.75/0.97        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 0.75/0.97      inference('demod', [status(thm)], ['2', '15', '16'])).
% 0.75/0.97  thf('18', plain, (~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.75/0.97      inference('clc', [status(thm)], ['9', '13'])).
% 0.75/0.97  thf('19', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.97  thf('20', plain, (~ (zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A)),
% 0.75/0.97      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.97  thf('21', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.75/0.97      inference('clc', [status(thm)], ['17', '20'])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.97       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.97         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.75/0.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.75/0.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.97  thf('25', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('26', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.75/0.97      inference('sup+', [status(thm)], ['24', '25'])).
% 0.75/0.97  thf(t3_funct_2, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.97       ( ( v1_funct_1 @ A ) & 
% 0.75/0.97         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.75/0.97         ( m1_subset_1 @
% 0.75/0.97           A @ 
% 0.75/0.97           ( k1_zfmisc_1 @
% 0.75/0.97             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.75/0.97  thf('27', plain,
% 0.75/0.97      (![X40 : $i]:
% 0.75/0.97         ((m1_subset_1 @ X40 @ 
% 0.75/0.97           (k1_zfmisc_1 @ 
% 0.75/0.97            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 0.75/0.97          | ~ (v1_funct_1 @ X40)
% 0.75/0.97          | ~ (v1_relat_1 @ X40))),
% 0.75/0.97      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.75/0.97  thf('28', plain,
% 0.75/0.97      (((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.75/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.97        | ~ (v1_funct_1 @ sk_C_1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['26', '27'])).
% 0.75/0.97  thf('29', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(cc1_relset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.97       ( v1_relat_1 @ C ) ))).
% 0.75/0.97  thf('30', plain,
% 0.75/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.97         ((v1_relat_1 @ X20)
% 0.75/0.97          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.75/0.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.97  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.97      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.97  thf('32', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('33', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.75/0.97      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.75/0.97  thf('34', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.97         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.75/0.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.75/0.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.97  thf('35', plain,
% 0.75/0.97      (((k1_relset_1 @ sk_A @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 0.75/0.97         = (k1_relat_1 @ sk_C_1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.97  thf('36', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.75/0.97      inference('sup+', [status(thm)], ['24', '25'])).
% 0.75/0.97  thf('37', plain,
% 0.75/0.97      (((k1_relset_1 @ sk_A @ (k2_relat_1 @ sk_C_1) @ sk_C_1) = (sk_A))),
% 0.75/0.97      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.97  thf('38', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(t10_subset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.97       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.75/0.97            ( ![C:$i]:
% 0.75/0.97              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.75/0.97  thf('39', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i]:
% 0.75/0.97         ((r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 0.75/0.97          | ((X8) = (k1_xboole_0))
% 0.75/0.97          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.75/0.97  thf('40', plain,
% 0.75/0.97      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.97        | (r2_hidden @ (sk_C @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_C_1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.97  thf('41', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.97  thf(t113_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.75/0.97       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.97  thf('42', plain,
% 0.75/0.97      (![X4 : $i, X5 : $i]:
% 0.75/0.97         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.97  thf('43', plain,
% 0.75/0.97      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['42'])).
% 0.75/0.97  thf('44', plain,
% 0.75/0.97      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.97        | (r2_hidden @ (sk_C @ sk_C_1 @ k1_xboole_0) @ sk_C_1))),
% 0.75/0.97      inference('demod', [status(thm)], ['40', '41', '43'])).
% 0.75/0.97  thf('45', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(t6_relset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.75/0.97       ( ~( ( r2_hidden @ A @ D ) & 
% 0.75/0.97            ( ![E:$i,F:$i]:
% 0.75/0.97              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.75/0.97                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.75/0.97  thf('46', plain,
% 0.75/0.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.75/0.97         ((r2_hidden @ (sk_F @ X26 @ X27 @ X28) @ X26)
% 0.75/0.97          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.75/0.97          | ~ (r2_hidden @ X28 @ X29))),
% 0.75/0.97      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.75/0.97  thf('47', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.75/0.97          | (r2_hidden @ (sk_F @ sk_B @ sk_A @ X0) @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.97  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.97  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.97  thf('50', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.75/0.97          | (r2_hidden @ (sk_F @ k1_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.75/0.97  thf(t60_relat_1, axiom,
% 0.75/0.97    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.75/0.97     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.97  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.97  thf(t118_funct_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.75/0.97       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.75/0.97           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.75/0.97         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.75/0.97           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.75/0.97  thf('52', plain,
% 0.75/0.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.75/0.97          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.75/0.97          | ((k9_relat_1 @ X15 @ (k2_tarski @ X14 @ X16))
% 0.75/0.97              = (k2_tarski @ (k1_funct_1 @ X15 @ X14) @ 
% 0.75/0.97                 (k1_funct_1 @ X15 @ X16)))
% 0.75/0.97          | ~ (v1_funct_1 @ X15)
% 0.75/0.97          | ~ (v1_relat_1 @ X15))),
% 0.75/0.97      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.75/0.97  thf('53', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.75/0.97          | ((k9_relat_1 @ k1_xboole_0 @ (k2_tarski @ X0 @ X1))
% 0.75/0.97              = (k2_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0) @ 
% 0.75/0.97                 (k1_funct_1 @ k1_xboole_0 @ X1)))
% 0.75/0.97          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['51', '52'])).
% 0.75/0.97  thf('54', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(t110_relat_1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.97  thf('55', plain,
% 0.75/0.97      (![X10 : $i]:
% 0.75/0.97         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.97          | ~ (v1_relat_1 @ X10))),
% 0.75/0.97      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.75/0.97  thf(fc8_funct_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.97       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.75/0.97         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.75/0.97  thf('56', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (~ (v1_funct_1 @ X12)
% 0.75/0.97          | ~ (v1_relat_1 @ X12)
% 0.75/0.97          | (v1_funct_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.97      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.75/0.97  thf('57', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((v1_funct_1 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | ~ (v1_funct_1 @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['55', '56'])).
% 0.75/0.97  thf('58', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_funct_1 @ X0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | (v1_funct_1 @ k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['57'])).
% 0.75/0.97  thf('59', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_C_1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['54', '58'])).
% 0.75/0.97  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.97      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.97  thf('61', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.75/0.97      inference('demod', [status(thm)], ['59', '60'])).
% 0.75/0.97  thf(t150_relat_1, axiom,
% 0.75/0.97    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.75/0.97  thf('62', plain,
% 0.75/0.97      (![X11 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.75/0.97  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.97  thf('64', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.97          | ((k1_xboole_0)
% 0.75/0.97              = (k2_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0) @ 
% 0.75/0.97                 (k1_funct_1 @ k1_xboole_0 @ X1)))
% 0.75/0.97          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['53', '61', '62', '63'])).
% 0.75/0.97  thf(t41_enumset1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k2_tarski @ A @ B ) =
% 0.75/0.97       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.75/0.97  thf('65', plain,
% 0.75/0.97      (![X1 : $i, X2 : $i]:
% 0.75/0.97         ((k2_tarski @ X1 @ X2)
% 0.75/0.97           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X2)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.75/0.97  thf(t49_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.75/0.97  thf('66', plain,
% 0.75/0.97      (![X6 : $i, X7 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.75/0.97  thf('67', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.97  thf('68', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.97          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.75/0.97      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 0.75/0.97  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('70', plain,
% 0.75/0.97      (![X10 : $i]:
% 0.75/0.97         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.97          | ~ (v1_relat_1 @ X10))),
% 0.75/0.97      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.75/0.97  thf('71', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (~ (v1_funct_1 @ X12)
% 0.75/0.97          | ~ (v1_relat_1 @ X12)
% 0.75/0.97          | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.75/0.97      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.75/0.97  thf('72', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((v1_relat_1 @ k1_xboole_0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | ~ (v1_funct_1 @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['70', '71'])).
% 0.75/0.97  thf('73', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_funct_1 @ X0)
% 0.75/0.97          | ~ (v1_relat_1 @ X0)
% 0.75/0.97          | (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['72'])).
% 0.75/0.97  thf('74', plain, (((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_C_1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['69', '73'])).
% 0.75/0.97  thf('75', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.97      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.97  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.97      inference('demod', [status(thm)], ['74', '75'])).
% 0.75/0.97  thf('77', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['68', '76'])).
% 0.75/0.97  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.97      inference('condensation', [status(thm)], ['77'])).
% 0.75/0.97  thf('79', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.75/0.97      inference('clc', [status(thm)], ['50', '78'])).
% 0.75/0.97  thf('80', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['44', '79'])).
% 0.75/0.97  thf('81', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.97  thf('82', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['44', '79'])).
% 0.75/0.97  thf('83', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.97  thf('84', plain,
% 0.75/0.97      (![X40 : $i]:
% 0.75/0.97         ((m1_subset_1 @ X40 @ 
% 0.75/0.97           (k1_zfmisc_1 @ 
% 0.75/0.97            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 0.75/0.97          | ~ (v1_funct_1 @ X40)
% 0.75/0.97          | ~ (v1_relat_1 @ X40))),
% 0.75/0.97      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.75/0.97  thf('85', plain,
% 0.75/0.97      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.75/0.97         (k1_zfmisc_1 @ 
% 0.75/0.97          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))))
% 0.75/0.97        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.97        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['83', '84'])).
% 0.75/0.97  thf('86', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.97  thf('87', plain,
% 0.75/0.97      (![X4 : $i, X5 : $i]:
% 0.75/0.97         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.97  thf('88', plain,
% 0.75/0.97      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['87'])).
% 0.75/0.97  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.97      inference('demod', [status(thm)], ['74', '75'])).
% 0.75/0.97  thf('90', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.75/0.97      inference('demod', [status(thm)], ['59', '60'])).
% 0.75/0.97  thf('91', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['85', '86', '88', '89', '90'])).
% 0.75/0.97  thf('92', plain,
% 0.75/0.97      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['42'])).
% 0.75/0.97  thf('93', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.97         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.75/0.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.75/0.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.97  thf('94', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.75/0.97          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_relat_1 @ X1)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['92', '93'])).
% 0.75/0.97  thf('95', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.97           = (k1_relat_1 @ k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['91', '94'])).
% 0.75/0.97  thf('96', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.97  thf('97', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['95', '96'])).
% 0.75/0.97  thf('98', plain, (((k1_xboole_0) = (sk_A))),
% 0.75/0.97      inference('demod', [status(thm)], ['37', '80', '81', '82', '97'])).
% 0.75/0.97  thf('99', plain,
% 0.75/0.97      (![X30 : $i, X31 : $i]:
% 0.75/0.97         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.97  thf('100', plain,
% 0.75/0.97      (![X30 : $i, X31 : $i]:
% 0.75/0.97         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.97  thf('101', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 0.75/0.97      inference('simplify', [status(thm)], ['100'])).
% 0.75/0.97  thf('102', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.75/0.97      inference('sup+', [status(thm)], ['99', '101'])).
% 0.75/0.97  thf('103', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.75/0.97      inference('eq_fact', [status(thm)], ['102'])).
% 0.75/0.97  thf('104', plain, ($false),
% 0.75/0.97      inference('demod', [status(thm)], ['21', '98', '103'])).
% 0.75/0.97  
% 0.75/0.97  % SZS output end Refutation
% 0.75/0.97  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
