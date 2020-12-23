%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wJz3hIgjmB

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:05 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  270 (5180 expanded)
%              Number of leaves         :   38 (1446 expanded)
%              Depth                    :   34
%              Number of atoms          : 1935 (67340 expanded)
%              Number of equality atoms :  158 (5073 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('34',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['29','32','33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['26','34'])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['24','35'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('39',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('52',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['24','35'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('76',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('81',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('82',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('85',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','90'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('92',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','90'])).

thf('97',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('108',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('109',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','112'])).

thf('114',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','113'])).

thf('115',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('116',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
        | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('120',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['107','108'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('125',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('126',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('129',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['107','108'])).

thf('132',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('134',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','134','135'])).

thf('137',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','139'])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('142',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('143',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('145',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','90'])).

thf('147',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('149',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['25'])).

thf('150',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','151'])).

thf('153',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('154',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('155',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('156',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('157',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('160',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('161',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('162',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['29','152','159','160','161'])).

thf('163',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','162'])).

thf('164',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['58','163'])).

thf('165',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','164'])).

thf('166',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('167',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('168',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('170',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('171',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['58','163'])).

thf('172',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('173',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('175',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('179',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['169','179'])).

thf('181',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','162'])).

thf('182',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('183',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['168','182'])).

thf('184',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['165','183'])).

thf('185',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('187',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('188',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('189',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['187','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('199',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['197','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['180','181'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['186','209'])).

thf('211',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('212',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','134','135'])).

thf('214',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['212','217'])).

thf('219',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['221'])).

thf('223',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('224',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('225',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['223','228'])).

thf('230',plain,(
    $false ),
    inference(demod,[status(thm)],['185','222','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wJz3hIgjmB
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.50/1.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.50/1.72  % Solved by: fo/fo7.sh
% 1.50/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.72  % done 2269 iterations in 1.266s
% 1.50/1.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.50/1.72  % SZS output start Refutation
% 1.50/1.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.50/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.50/1.72  thf(sk_C_type, type, sk_C: $i).
% 1.50/1.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.50/1.72  thf(sk_D_type, type, sk_D: $i).
% 1.50/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.50/1.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.50/1.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.50/1.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.50/1.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.50/1.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.50/1.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.50/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.50/1.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.50/1.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.50/1.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.50/1.72  thf(t8_funct_2, conjecture,
% 1.50/1.72    (![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.50/1.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.50/1.72       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.50/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.50/1.72           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.50/1.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.50/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.50/1.72            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.50/1.72          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.50/1.72            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.50/1.72              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.50/1.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.50/1.72    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.50/1.72  thf('0', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('1', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf(redefinition_k2_relset_1, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.50/1.72  thf('2', plain,
% 1.50/1.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.50/1.72         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.50/1.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.50/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.50/1.72  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.50/1.72      inference('sup-', [status(thm)], ['1', '2'])).
% 1.50/1.72  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.50/1.72      inference('demod', [status(thm)], ['0', '3'])).
% 1.50/1.72  thf('5', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf(cc2_relset_1, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.50/1.72  thf('6', plain,
% 1.50/1.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.50/1.72         ((v4_relat_1 @ X20 @ X21)
% 1.50/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.50/1.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.72  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.50/1.72      inference('sup-', [status(thm)], ['5', '6'])).
% 1.50/1.72  thf(d18_relat_1, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( v1_relat_1 @ B ) =>
% 1.50/1.72       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.50/1.72  thf('8', plain,
% 1.50/1.72      (![X11 : $i, X12 : $i]:
% 1.50/1.72         (~ (v4_relat_1 @ X11 @ X12)
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.50/1.72          | ~ (v1_relat_1 @ X11))),
% 1.50/1.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.50/1.72  thf('9', plain,
% 1.50/1.72      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.50/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.50/1.72  thf('10', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf(cc2_relat_1, axiom,
% 1.50/1.72    (![A:$i]:
% 1.50/1.72     ( ( v1_relat_1 @ A ) =>
% 1.50/1.72       ( ![B:$i]:
% 1.50/1.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.50/1.72  thf('11', plain,
% 1.50/1.72      (![X9 : $i, X10 : $i]:
% 1.50/1.72         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 1.50/1.72          | (v1_relat_1 @ X9)
% 1.50/1.72          | ~ (v1_relat_1 @ X10))),
% 1.50/1.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.50/1.72  thf('12', plain,
% 1.50/1.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.50/1.72      inference('sup-', [status(thm)], ['10', '11'])).
% 1.50/1.72  thf(fc6_relat_1, axiom,
% 1.50/1.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.50/1.72  thf('13', plain,
% 1.50/1.72      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.50/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.50/1.72  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.72      inference('demod', [status(thm)], ['12', '13'])).
% 1.50/1.72  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.50/1.72      inference('demod', [status(thm)], ['9', '14'])).
% 1.50/1.72  thf(t11_relset_1, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( v1_relat_1 @ C ) =>
% 1.50/1.72       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.50/1.72           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.50/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.50/1.72  thf('16', plain,
% 1.50/1.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.50/1.72         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 1.50/1.72          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.50/1.72          | ~ (v1_relat_1 @ X29))),
% 1.50/1.72      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.50/1.72  thf('17', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ sk_D)
% 1.50/1.72          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['15', '16'])).
% 1.50/1.72  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.72      inference('demod', [status(thm)], ['12', '13'])).
% 1.50/1.72  thf('19', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.50/1.72      inference('demod', [status(thm)], ['17', '18'])).
% 1.50/1.72  thf('20', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['4', '19'])).
% 1.50/1.72  thf(redefinition_k1_relset_1, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.50/1.72  thf('21', plain,
% 1.50/1.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.50/1.72         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.50/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.50/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.50/1.72  thf('22', plain,
% 1.50/1.72      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.50/1.72      inference('sup-', [status(thm)], ['20', '21'])).
% 1.50/1.72  thf(d1_funct_2, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.50/1.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.50/1.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.50/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.50/1.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.50/1.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.50/1.72  thf(zf_stmt_1, axiom,
% 1.50/1.72    (![C:$i,B:$i,A:$i]:
% 1.50/1.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.50/1.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.50/1.72  thf('23', plain,
% 1.50/1.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.50/1.72         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 1.50/1.72          | (v1_funct_2 @ X36 @ X34 @ X35)
% 1.50/1.72          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.50/1.72  thf('24', plain,
% 1.50/1.72      ((((sk_A) != (k1_relat_1 @ sk_D))
% 1.50/1.72        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 1.50/1.72        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.50/1.72      inference('sup-', [status(thm)], ['22', '23'])).
% 1.50/1.72  thf('25', plain,
% 1.50/1.72      ((~ (v1_funct_1 @ sk_D)
% 1.50/1.72        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.50/1.72        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('26', plain,
% 1.50/1.72      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.50/1.72         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('28', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('29', plain, (((v1_funct_1 @ sk_D))),
% 1.50/1.72      inference('sup-', [status(thm)], ['27', '28'])).
% 1.50/1.72  thf('30', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['4', '19'])).
% 1.50/1.72  thf('31', plain,
% 1.50/1.72      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.50/1.72         <= (~
% 1.50/1.72             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('32', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['30', '31'])).
% 1.50/1.72  thf('33', plain,
% 1.50/1.72      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 1.50/1.72       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.50/1.72       ~ ((v1_funct_1 @ sk_D))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('34', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.50/1.72      inference('sat_resolution*', [status(thm)], ['29', '32', '33'])).
% 1.50/1.72  thf('35', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 1.50/1.72      inference('simpl_trail', [status(thm)], ['26', '34'])).
% 1.50/1.72  thf('36', plain,
% 1.50/1.72      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 1.50/1.72        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('clc', [status(thm)], ['24', '35'])).
% 1.50/1.72  thf(zf_stmt_2, axiom,
% 1.50/1.72    (![B:$i,A:$i]:
% 1.50/1.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.50/1.72       ( zip_tseitin_0 @ B @ A ) ))).
% 1.50/1.72  thf('37', plain,
% 1.50/1.72      (![X32 : $i, X33 : $i]:
% 1.50/1.72         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.50/1.72  thf('38', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.50/1.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.50/1.72  thf(zf_stmt_5, axiom,
% 1.50/1.72    (![A:$i,B:$i,C:$i]:
% 1.50/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.50/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.50/1.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.50/1.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.50/1.72  thf('39', plain,
% 1.50/1.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.72         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.50/1.72          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.50/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.50/1.72  thf('40', plain,
% 1.50/1.72      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.50/1.72      inference('sup-', [status(thm)], ['38', '39'])).
% 1.50/1.72  thf('41', plain,
% 1.50/1.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.50/1.72      inference('sup-', [status(thm)], ['37', '40'])).
% 1.50/1.72  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('43', plain,
% 1.50/1.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.50/1.72         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 1.50/1.72          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 1.50/1.72          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.50/1.72  thf('44', plain,
% 1.50/1.72      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.50/1.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['42', '43'])).
% 1.50/1.72  thf('45', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('46', plain,
% 1.50/1.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.50/1.72         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.50/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.50/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.50/1.72  thf('47', plain,
% 1.50/1.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.50/1.72      inference('sup-', [status(thm)], ['45', '46'])).
% 1.50/1.72  thf('48', plain,
% 1.50/1.72      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('demod', [status(thm)], ['44', '47'])).
% 1.50/1.72  thf('49', plain,
% 1.50/1.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['41', '48'])).
% 1.50/1.72  thf('50', plain,
% 1.50/1.72      (![X32 : $i, X33 : $i]:
% 1.50/1.72         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.50/1.72  thf('51', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['4', '19'])).
% 1.50/1.72  thf('52', plain,
% 1.50/1.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.72         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.50/1.72          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.50/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.50/1.72  thf('53', plain,
% 1.50/1.72      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 1.50/1.72      inference('sup-', [status(thm)], ['51', '52'])).
% 1.50/1.72  thf('54', plain,
% 1.50/1.72      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 1.50/1.72      inference('sup-', [status(thm)], ['50', '53'])).
% 1.50/1.72  thf('55', plain,
% 1.50/1.72      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 1.50/1.72        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('clc', [status(thm)], ['24', '35'])).
% 1.50/1.72  thf('56', plain,
% 1.50/1.72      ((((sk_C) = (k1_xboole_0)) | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['54', '55'])).
% 1.50/1.72  thf('57', plain,
% 1.50/1.72      ((((sk_A) != (sk_A))
% 1.50/1.72        | ((sk_B) = (k1_xboole_0))
% 1.50/1.72        | ((sk_C) = (k1_xboole_0)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['49', '56'])).
% 1.50/1.72  thf('58', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.50/1.72      inference('simplify', [status(thm)], ['57'])).
% 1.50/1.72  thf('59', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('60', plain,
% 1.50/1.72      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.50/1.72      inference('split', [status(esa)], ['59'])).
% 1.50/1.72  thf(t113_zfmisc_1, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.50/1.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.50/1.72  thf('61', plain,
% 1.50/1.72      (![X4 : $i, X5 : $i]:
% 1.50/1.72         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.50/1.72  thf('62', plain,
% 1.50/1.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['61'])).
% 1.50/1.72  thf('63', plain,
% 1.50/1.72      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('split', [status(esa)], ['59'])).
% 1.50/1.72  thf('64', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('65', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ 
% 1.50/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['63', '64'])).
% 1.50/1.72  thf('66', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['62', '65'])).
% 1.50/1.72  thf('67', plain,
% 1.50/1.72      (![X4 : $i, X5 : $i]:
% 1.50/1.72         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.50/1.72  thf('68', plain,
% 1.50/1.72      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['67'])).
% 1.50/1.72  thf('69', plain,
% 1.50/1.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.50/1.72         ((v4_relat_1 @ X20 @ X21)
% 1.50/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.50/1.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.72  thf('70', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.50/1.72          | (v4_relat_1 @ X1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['68', '69'])).
% 1.50/1.72  thf('71', plain,
% 1.50/1.72      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['66', '70'])).
% 1.50/1.72  thf('72', plain,
% 1.50/1.72      (![X11 : $i, X12 : $i]:
% 1.50/1.72         (~ (v4_relat_1 @ X11 @ X12)
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.50/1.72          | ~ (v1_relat_1 @ X11))),
% 1.50/1.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.50/1.72  thf('73', plain,
% 1.50/1.72      ((![X0 : $i]:
% 1.50/1.72          (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['71', '72'])).
% 1.50/1.72  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.72      inference('demod', [status(thm)], ['12', '13'])).
% 1.50/1.72  thf('75', plain,
% 1.50/1.72      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('split', [status(esa)], ['59'])).
% 1.50/1.72  thf('76', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.72  thf('77', plain,
% 1.50/1.72      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['75', '76'])).
% 1.50/1.72  thf('78', plain,
% 1.50/1.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.50/1.72         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 1.50/1.72          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 1.50/1.72          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.50/1.72  thf('79', plain,
% 1.50/1.72      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.50/1.72         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['77', '78'])).
% 1.50/1.72  thf('80', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ 
% 1.50/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['63', '64'])).
% 1.50/1.72  thf('81', plain,
% 1.50/1.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.50/1.72         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.50/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.50/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.50/1.72  thf('82', plain,
% 1.50/1.72      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['80', '81'])).
% 1.50/1.72  thf('83', plain,
% 1.50/1.72      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.50/1.72         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['79', '82'])).
% 1.50/1.72  thf('84', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ 
% 1.50/1.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['63', '64'])).
% 1.50/1.72  thf('85', plain,
% 1.50/1.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.72         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.50/1.72          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.50/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.50/1.72  thf('86', plain,
% 1.50/1.72      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.50/1.72         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['84', '85'])).
% 1.50/1.72  thf('87', plain,
% 1.50/1.72      (![X32 : $i, X33 : $i]:
% 1.50/1.72         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.50/1.72  thf('88', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 1.50/1.72      inference('simplify', [status(thm)], ['87'])).
% 1.50/1.72  thf('89', plain,
% 1.50/1.72      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['86', '88'])).
% 1.50/1.72  thf('90', plain,
% 1.50/1.72      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['83', '89'])).
% 1.50/1.72  thf('91', plain,
% 1.50/1.72      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['73', '74', '90'])).
% 1.50/1.72  thf(t3_subset, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.50/1.72  thf('92', plain,
% 1.50/1.72      (![X6 : $i, X8 : $i]:
% 1.50/1.72         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.50/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.72  thf('93', plain,
% 1.50/1.72      ((![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['91', '92'])).
% 1.50/1.72  thf('94', plain,
% 1.50/1.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.50/1.72         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.50/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.50/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.50/1.72  thf('95', plain,
% 1.50/1.72      ((![X0 : $i, X1 : $i]:
% 1.50/1.72          ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['93', '94'])).
% 1.50/1.72  thf('96', plain,
% 1.50/1.72      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['73', '74', '90'])).
% 1.50/1.72  thf('97', plain,
% 1.50/1.72      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['67'])).
% 1.50/1.72  thf(d10_xboole_0, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.72  thf('98', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.50/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.72  thf('99', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.50/1.72      inference('simplify', [status(thm)], ['98'])).
% 1.50/1.72  thf('100', plain,
% 1.50/1.72      (![X6 : $i, X8 : $i]:
% 1.50/1.72         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.50/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.72  thf('101', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['99', '100'])).
% 1.50/1.72  thf('102', plain,
% 1.50/1.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.50/1.72         ((v4_relat_1 @ X20 @ X21)
% 1.50/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.50/1.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.72  thf('103', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.50/1.72      inference('sup-', [status(thm)], ['101', '102'])).
% 1.50/1.72  thf('104', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.50/1.72      inference('sup+', [status(thm)], ['97', '103'])).
% 1.50/1.72  thf('105', plain,
% 1.50/1.72      (![X11 : $i, X12 : $i]:
% 1.50/1.72         (~ (v4_relat_1 @ X11 @ X12)
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.50/1.72          | ~ (v1_relat_1 @ X11))),
% 1.50/1.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.50/1.72  thf('106', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ k1_xboole_0)
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['104', '105'])).
% 1.50/1.72  thf('107', plain,
% 1.50/1.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['61'])).
% 1.50/1.72  thf('108', plain,
% 1.50/1.72      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.50/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.50/1.72  thf('109', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.50/1.72      inference('sup+', [status(thm)], ['107', '108'])).
% 1.50/1.72  thf('110', plain,
% 1.50/1.72      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['106', '109'])).
% 1.50/1.72  thf('111', plain,
% 1.50/1.72      (![X0 : $i, X2 : $i]:
% 1.50/1.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.72  thf('112', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.50/1.72          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['110', '111'])).
% 1.50/1.72  thf('113', plain,
% 1.50/1.72      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['96', '112'])).
% 1.50/1.72  thf('114', plain,
% 1.50/1.72      ((![X0 : $i, X1 : $i]:
% 1.50/1.72          ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['95', '113'])).
% 1.50/1.72  thf('115', plain,
% 1.50/1.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.50/1.72         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 1.50/1.72          | (v1_funct_2 @ X36 @ X34 @ X35)
% 1.50/1.72          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.50/1.72  thf('116', plain,
% 1.50/1.72      ((![X0 : $i, X1 : $i]:
% 1.50/1.72          (((X1) != (k1_xboole_0))
% 1.50/1.72           | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.50/1.72           | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['114', '115'])).
% 1.50/1.72  thf('117', plain,
% 1.50/1.72      ((![X0 : $i]:
% 1.50/1.72          ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.50/1.72           | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('simplify', [status(thm)], ['116'])).
% 1.50/1.72  thf('118', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 1.50/1.72      inference('simplify', [status(thm)], ['87'])).
% 1.50/1.72  thf('119', plain,
% 1.50/1.72      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['106', '109'])).
% 1.50/1.72  thf('120', plain,
% 1.50/1.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.50/1.72         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 1.50/1.72          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.50/1.72          | ~ (v1_relat_1 @ X29))),
% 1.50/1.72      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.50/1.72  thf('121', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ k1_xboole_0)
% 1.50/1.72          | (m1_subset_1 @ k1_xboole_0 @ 
% 1.50/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1))),
% 1.50/1.72      inference('sup-', [status(thm)], ['119', '120'])).
% 1.50/1.72  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.50/1.72      inference('sup+', [status(thm)], ['107', '108'])).
% 1.50/1.72  thf('123', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1))),
% 1.50/1.72      inference('demod', [status(thm)], ['121', '122'])).
% 1.50/1.72  thf('124', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['99', '100'])).
% 1.50/1.72  thf('125', plain,
% 1.50/1.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['61'])).
% 1.50/1.72  thf('126', plain,
% 1.50/1.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.50/1.72         ((v5_relat_1 @ X20 @ X22)
% 1.50/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.50/1.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.72  thf('127', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.50/1.72          | (v5_relat_1 @ X1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['125', '126'])).
% 1.50/1.72  thf('128', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 1.50/1.72      inference('sup-', [status(thm)], ['124', '127'])).
% 1.50/1.72  thf(d19_relat_1, axiom,
% 1.50/1.72    (![A:$i,B:$i]:
% 1.50/1.72     ( ( v1_relat_1 @ B ) =>
% 1.50/1.72       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.50/1.72  thf('129', plain,
% 1.50/1.72      (![X13 : $i, X14 : $i]:
% 1.50/1.72         (~ (v5_relat_1 @ X13 @ X14)
% 1.50/1.72          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.50/1.72          | ~ (v1_relat_1 @ X13))),
% 1.50/1.72      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.50/1.72  thf('130', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ k1_xboole_0)
% 1.50/1.72          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['128', '129'])).
% 1.50/1.72  thf('131', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.50/1.72      inference('sup+', [status(thm)], ['107', '108'])).
% 1.50/1.72  thf('132', plain,
% 1.50/1.72      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['130', '131'])).
% 1.50/1.72  thf('133', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.50/1.72          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['110', '111'])).
% 1.50/1.72  thf('134', plain,
% 1.50/1.72      (((k2_relat_1 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['132', '133'])).
% 1.50/1.72  thf('135', plain,
% 1.50/1.72      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['106', '109'])).
% 1.50/1.72  thf('136', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.50/1.72      inference('demod', [status(thm)], ['123', '134', '135'])).
% 1.50/1.72  thf('137', plain,
% 1.50/1.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.72         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.50/1.72          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.50/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.50/1.72  thf('138', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.50/1.72      inference('sup-', [status(thm)], ['136', '137'])).
% 1.50/1.72  thf('139', plain,
% 1.50/1.72      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.50/1.72      inference('sup-', [status(thm)], ['118', '138'])).
% 1.50/1.72  thf('140', plain,
% 1.50/1.72      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['117', '139'])).
% 1.50/1.72  thf('141', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['62', '65'])).
% 1.50/1.72  thf('142', plain,
% 1.50/1.72      (![X6 : $i, X7 : $i]:
% 1.50/1.72         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.72  thf('143', plain,
% 1.50/1.72      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['141', '142'])).
% 1.50/1.72  thf('144', plain,
% 1.50/1.72      (![X0 : $i, X2 : $i]:
% 1.50/1.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.72  thf('145', plain,
% 1.50/1.72      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['143', '144'])).
% 1.50/1.72  thf('146', plain,
% 1.50/1.72      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['73', '74', '90'])).
% 1.50/1.72  thf('147', plain,
% 1.50/1.72      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('demod', [status(thm)], ['145', '146'])).
% 1.50/1.72  thf('148', plain,
% 1.50/1.72      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('split', [status(esa)], ['59'])).
% 1.50/1.72  thf('149', plain,
% 1.50/1.72      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.50/1.72         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('150', plain,
% 1.50/1.72      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 1.50/1.72         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['148', '149'])).
% 1.50/1.72  thf('151', plain,
% 1.50/1.72      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.50/1.72         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['147', '150'])).
% 1.50/1.72  thf('152', plain,
% 1.50/1.72      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['140', '151'])).
% 1.50/1.72  thf('153', plain,
% 1.50/1.72      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.50/1.72         <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup+', [status(thm)], ['62', '65'])).
% 1.50/1.72  thf('154', plain,
% 1.50/1.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['61'])).
% 1.50/1.72  thf('155', plain,
% 1.50/1.72      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('split', [status(esa)], ['59'])).
% 1.50/1.72  thf('156', plain,
% 1.50/1.72      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.50/1.72         <= (~
% 1.50/1.72             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('157', plain,
% 1.50/1.72      ((~ (m1_subset_1 @ sk_D @ 
% 1.50/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.50/1.72         <= (~
% 1.50/1.72             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.50/1.72             (((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['155', '156'])).
% 1.50/1.72  thf('158', plain,
% 1.50/1.72      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.50/1.72         <= (~
% 1.50/1.72             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.50/1.72             (((sk_A) = (k1_xboole_0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['154', '157'])).
% 1.50/1.72  thf('159', plain,
% 1.50/1.72      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.50/1.72       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['153', '158'])).
% 1.50/1.72  thf('160', plain,
% 1.50/1.72      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.50/1.72       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 1.50/1.72      inference('split', [status(esa)], ['25'])).
% 1.50/1.72  thf('161', plain,
% 1.50/1.72      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.50/1.72      inference('split', [status(esa)], ['59'])).
% 1.50/1.72  thf('162', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.50/1.72      inference('sat_resolution*', [status(thm)],
% 1.50/1.72                ['29', '152', '159', '160', '161'])).
% 1.50/1.72  thf('163', plain, (((sk_B) != (k1_xboole_0))),
% 1.50/1.72      inference('simpl_trail', [status(thm)], ['60', '162'])).
% 1.50/1.72  thf('164', plain, (((sk_C) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify_reflect-', [status(thm)], ['58', '163'])).
% 1.50/1.72  thf('165', plain,
% 1.50/1.72      ((~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)
% 1.50/1.72        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('demod', [status(thm)], ['36', '164'])).
% 1.50/1.72  thf('166', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.50/1.72      inference('demod', [status(thm)], ['9', '14'])).
% 1.50/1.72  thf('167', plain,
% 1.50/1.72      (![X0 : $i, X2 : $i]:
% 1.50/1.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.72  thf('168', plain,
% 1.50/1.72      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_D))
% 1.50/1.72        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['166', '167'])).
% 1.50/1.72  thf('169', plain,
% 1.50/1.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['41', '48'])).
% 1.50/1.72  thf('170', plain,
% 1.50/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['4', '19'])).
% 1.50/1.72  thf('171', plain, (((sk_C) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify_reflect-', [status(thm)], ['58', '163'])).
% 1.50/1.72  thf('172', plain,
% 1.50/1.72      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['67'])).
% 1.50/1.72  thf('173', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.50/1.72      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.50/1.72  thf('174', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.50/1.72          | (v4_relat_1 @ X1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['68', '69'])).
% 1.50/1.72  thf('175', plain, (![X0 : $i]: (v4_relat_1 @ sk_D @ X0)),
% 1.50/1.72      inference('sup-', [status(thm)], ['173', '174'])).
% 1.50/1.72  thf('176', plain,
% 1.50/1.72      (![X11 : $i, X12 : $i]:
% 1.50/1.72         (~ (v4_relat_1 @ X11 @ X12)
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.50/1.72          | ~ (v1_relat_1 @ X11))),
% 1.50/1.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.50/1.72  thf('177', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['175', '176'])).
% 1.50/1.72  thf('178', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.72      inference('demod', [status(thm)], ['12', '13'])).
% 1.50/1.72  thf('179', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_D) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['177', '178'])).
% 1.50/1.72  thf('180', plain,
% 1.50/1.72      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_B) = (k1_xboole_0)))),
% 1.50/1.72      inference('sup+', [status(thm)], ['169', '179'])).
% 1.50/1.72  thf('181', plain, (((sk_B) != (k1_xboole_0))),
% 1.50/1.72      inference('simpl_trail', [status(thm)], ['60', '162'])).
% 1.50/1.72  thf('182', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 1.50/1.72      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 1.50/1.72  thf('183', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.50/1.72      inference('demod', [status(thm)], ['168', '182'])).
% 1.50/1.72  thf('184', plain,
% 1.50/1.72      ((~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A) | ((sk_A) != (sk_A)))),
% 1.50/1.72      inference('demod', [status(thm)], ['165', '183'])).
% 1.50/1.72  thf('185', plain, (~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)),
% 1.50/1.72      inference('simplify', [status(thm)], ['184'])).
% 1.50/1.72  thf('186', plain,
% 1.50/1.72      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['67'])).
% 1.50/1.72  thf('187', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 1.50/1.72      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 1.50/1.72  thf('188', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['99', '100'])).
% 1.50/1.72  thf('189', plain,
% 1.50/1.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.50/1.72         ((v5_relat_1 @ X20 @ X22)
% 1.50/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.50/1.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.72  thf('190', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 1.50/1.72      inference('sup-', [status(thm)], ['188', '189'])).
% 1.50/1.72  thf('191', plain,
% 1.50/1.72      (![X13 : $i, X14 : $i]:
% 1.50/1.72         (~ (v5_relat_1 @ X13 @ X14)
% 1.50/1.72          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.50/1.72          | ~ (v1_relat_1 @ X13))),
% 1.50/1.72      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.50/1.72  thf('192', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.50/1.72          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['190', '191'])).
% 1.50/1.72  thf('193', plain,
% 1.50/1.72      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.50/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.50/1.72  thf('194', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['192', '193'])).
% 1.50/1.72  thf('195', plain,
% 1.50/1.72      (![X0 : $i, X2 : $i]:
% 1.50/1.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.72  thf('196', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.50/1.72          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['194', '195'])).
% 1.50/1.72  thf('197', plain,
% 1.50/1.72      (![X0 : $i]: ((sk_A) = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['187', '196'])).
% 1.50/1.72  thf('198', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.50/1.72      inference('sup-', [status(thm)], ['101', '102'])).
% 1.50/1.72  thf('199', plain,
% 1.50/1.72      (![X11 : $i, X12 : $i]:
% 1.50/1.72         (~ (v4_relat_1 @ X11 @ X12)
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.50/1.72          | ~ (v1_relat_1 @ X11))),
% 1.50/1.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.50/1.72  thf('200', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.50/1.72          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['198', '199'])).
% 1.50/1.72  thf('201', plain,
% 1.50/1.72      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.50/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.50/1.72  thf('202', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.50/1.72      inference('demod', [status(thm)], ['200', '201'])).
% 1.50/1.72  thf('203', plain,
% 1.50/1.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.50/1.72         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 1.50/1.72          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.50/1.72          | ~ (v1_relat_1 @ X29))),
% 1.50/1.72      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.50/1.72  thf('204', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.72         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.50/1.72          | (m1_subset_1 @ (k2_zfmisc_1 @ X0 @ X1) @ 
% 1.50/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2))),
% 1.50/1.72      inference('sup-', [status(thm)], ['202', '203'])).
% 1.50/1.72  thf('205', plain,
% 1.50/1.72      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.50/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.50/1.72  thf('206', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.72         ((m1_subset_1 @ (k2_zfmisc_1 @ X0 @ X1) @ 
% 1.50/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 1.50/1.72          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2))),
% 1.50/1.72      inference('demod', [status(thm)], ['204', '205'])).
% 1.50/1.72  thf('207', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (r1_tarski @ sk_A @ X0)
% 1.50/1.72          | (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ sk_A) @ 
% 1.50/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.50/1.72      inference('sup-', [status(thm)], ['197', '206'])).
% 1.50/1.72  thf('208', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 1.50/1.72      inference('simplify_reflect-', [status(thm)], ['180', '181'])).
% 1.50/1.72  thf('209', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ sk_A) @ 
% 1.50/1.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.50/1.72      inference('demod', [status(thm)], ['207', '208'])).
% 1.50/1.72  thf('210', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (m1_subset_1 @ (k2_zfmisc_1 @ X0 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.50/1.72      inference('sup+', [status(thm)], ['186', '209'])).
% 1.50/1.72  thf('211', plain,
% 1.50/1.72      (![X6 : $i, X7 : $i]:
% 1.50/1.72         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.72  thf('212', plain,
% 1.50/1.72      (![X0 : $i]: (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_A) @ k1_xboole_0)),
% 1.50/1.72      inference('sup-', [status(thm)], ['210', '211'])).
% 1.50/1.72  thf('213', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.50/1.72      inference('demod', [status(thm)], ['123', '134', '135'])).
% 1.50/1.72  thf('214', plain,
% 1.50/1.72      (![X6 : $i, X7 : $i]:
% 1.50/1.72         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.72  thf('215', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['213', '214'])).
% 1.50/1.72  thf('216', plain,
% 1.50/1.72      (![X0 : $i, X2 : $i]:
% 1.50/1.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.72  thf('217', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ k1_xboole_0)
% 1.50/1.72          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['215', '216'])).
% 1.50/1.72  thf('218', plain, (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_A) = (k1_xboole_0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['212', '217'])).
% 1.50/1.72  thf('219', plain,
% 1.50/1.72      (![X3 : $i, X4 : $i]:
% 1.50/1.72         (((X3) = (k1_xboole_0))
% 1.50/1.72          | ((X4) = (k1_xboole_0))
% 1.50/1.72          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 1.50/1.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.50/1.72  thf('220', plain,
% 1.50/1.72      (![X0 : $i]:
% 1.50/1.72         (((k1_xboole_0) != (k1_xboole_0))
% 1.50/1.72          | ((X0) = (k1_xboole_0))
% 1.50/1.72          | ((sk_A) = (k1_xboole_0)))),
% 1.50/1.72      inference('sup-', [status(thm)], ['218', '219'])).
% 1.50/1.72  thf('221', plain,
% 1.50/1.72      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 1.50/1.72      inference('simplify', [status(thm)], ['220'])).
% 1.50/1.72  thf('222', plain, (((sk_A) = (k1_xboole_0))),
% 1.50/1.72      inference('condensation', [status(thm)], ['221'])).
% 1.50/1.72  thf('223', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.50/1.72      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.50/1.72  thf('224', plain,
% 1.50/1.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.50/1.72      inference('simplify', [status(thm)], ['61'])).
% 1.50/1.72  thf('225', plain,
% 1.50/1.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.72         (~ (zip_tseitin_0 @ X37 @ X38)
% 1.50/1.72          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 1.50/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 1.50/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.50/1.72  thf('226', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.50/1.72          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.50/1.72          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.50/1.72      inference('sup-', [status(thm)], ['224', '225'])).
% 1.50/1.72  thf('227', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 1.50/1.72      inference('simplify', [status(thm)], ['87'])).
% 1.50/1.72  thf('228', plain,
% 1.50/1.72      (![X0 : $i, X1 : $i]:
% 1.50/1.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.50/1.72          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.50/1.72      inference('demod', [status(thm)], ['226', '227'])).
% 1.50/1.72  thf('229', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)),
% 1.50/1.72      inference('sup-', [status(thm)], ['223', '228'])).
% 1.50/1.72  thf('230', plain, ($false),
% 1.50/1.72      inference('demod', [status(thm)], ['185', '222', '229'])).
% 1.50/1.72  
% 1.50/1.72  % SZS output end Refutation
% 1.50/1.72  
% 1.50/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
