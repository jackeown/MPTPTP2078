%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L0iZSQM4Zl

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:52 EST 2020

% Result     : Theorem 9.27s
% Output     : Refutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 224 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  575 (2407 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('3',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','26','27'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['18','29'])).

thf('31',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['12','30'])).

thf('32',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','31'])).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('34',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','34'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('41',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['12','30'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(rc1_relset_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( v1_xboole_0 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_xboole_0 @ ( sk_C @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('46',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_xboole_0 @ ( sk_C @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','42','44','49'])).

thf('51',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['36','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['35','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L0iZSQM4Zl
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 9.27/9.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.27/9.51  % Solved by: fo/fo7.sh
% 9.27/9.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.27/9.51  % done 3235 iterations in 9.014s
% 9.27/9.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.27/9.51  % SZS output start Refutation
% 9.27/9.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.27/9.51  thf(sk_B_type, type, sk_B: $i > $i).
% 9.27/9.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.27/9.51  thf(sk_A_type, type, sk_A: $i).
% 9.27/9.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.27/9.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.27/9.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.27/9.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.27/9.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.27/9.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.27/9.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.27/9.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.27/9.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.27/9.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.27/9.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.27/9.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.27/9.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 9.27/9.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.27/9.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.27/9.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.27/9.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.27/9.51  thf(l13_xboole_0, axiom,
% 9.27/9.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.27/9.51  thf('0', plain,
% 9.27/9.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 9.27/9.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.27/9.51  thf(t60_relat_1, axiom,
% 9.27/9.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 9.27/9.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 9.27/9.51  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.27/9.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 9.27/9.51  thf('2', plain,
% 9.27/9.51      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 9.27/9.51      inference('sup+', [status(thm)], ['0', '1'])).
% 9.27/9.51  thf(t4_funct_2, conjecture,
% 9.27/9.51    (![A:$i,B:$i]:
% 9.27/9.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.27/9.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 9.27/9.51         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 9.27/9.51           ( m1_subset_1 @
% 9.27/9.51             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 9.27/9.51  thf(zf_stmt_0, negated_conjecture,
% 9.27/9.51    (~( ![A:$i,B:$i]:
% 9.27/9.51        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.27/9.51          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 9.27/9.51            ( ( v1_funct_1 @ B ) & 
% 9.27/9.51              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 9.27/9.51              ( m1_subset_1 @
% 9.27/9.51                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 9.27/9.51    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 9.27/9.51  thf('3', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.27/9.51  thf(d10_xboole_0, axiom,
% 9.27/9.51    (![A:$i,B:$i]:
% 9.27/9.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.27/9.51  thf('4', plain,
% 9.27/9.51      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 9.27/9.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.27/9.51  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 9.27/9.51      inference('simplify', [status(thm)], ['4'])).
% 9.27/9.51  thf(t11_relset_1, axiom,
% 9.27/9.51    (![A:$i,B:$i,C:$i]:
% 9.27/9.51     ( ( v1_relat_1 @ C ) =>
% 9.27/9.51       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 9.27/9.51           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 9.27/9.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 9.27/9.51  thf('6', plain,
% 9.27/9.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.27/9.51         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 9.27/9.51          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 9.27/9.51          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 9.27/9.51          | ~ (v1_relat_1 @ X23))),
% 9.27/9.51      inference('cnf', [status(esa)], [t11_relset_1])).
% 9.27/9.51  thf('7', plain,
% 9.27/9.51      (![X0 : $i, X1 : $i]:
% 9.27/9.51         (~ (v1_relat_1 @ X0)
% 9.27/9.51          | (m1_subset_1 @ X0 @ 
% 9.27/9.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 9.27/9.51          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 9.27/9.51      inference('sup-', [status(thm)], ['5', '6'])).
% 9.27/9.51  thf('8', plain,
% 9.27/9.51      (((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 9.27/9.51        | ~ (v1_relat_1 @ sk_B_1))),
% 9.27/9.51      inference('sup-', [status(thm)], ['3', '7'])).
% 9.27/9.51  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.27/9.51  thf('10', plain,
% 9.27/9.51      ((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 9.27/9.51      inference('demod', [status(thm)], ['8', '9'])).
% 9.27/9.51  thf(d1_funct_2, axiom,
% 9.27/9.51    (![A:$i,B:$i,C:$i]:
% 9.27/9.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.27/9.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.27/9.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 9.27/9.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 9.27/9.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.27/9.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 9.27/9.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 9.27/9.51  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.27/9.51  thf(zf_stmt_2, axiom,
% 9.27/9.51    (![C:$i,B:$i,A:$i]:
% 9.27/9.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.27/9.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 9.27/9.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 9.27/9.51  thf(zf_stmt_4, axiom,
% 9.27/9.51    (![B:$i,A:$i]:
% 9.27/9.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.27/9.51       ( zip_tseitin_0 @ B @ A ) ))).
% 9.27/9.51  thf(zf_stmt_5, axiom,
% 9.27/9.51    (![A:$i,B:$i,C:$i]:
% 9.27/9.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.27/9.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.27/9.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.27/9.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 9.27/9.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 9.27/9.51  thf('11', plain,
% 9.27/9.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.27/9.51         (~ (zip_tseitin_0 @ X31 @ X32)
% 9.27/9.51          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 9.27/9.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.27/9.51  thf('12', plain,
% 9.27/9.51      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 9.27/9.51        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 9.27/9.51      inference('sup-', [status(thm)], ['10', '11'])).
% 9.27/9.51  thf('13', plain,
% 9.27/9.51      ((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 9.27/9.51      inference('demod', [status(thm)], ['8', '9'])).
% 9.27/9.51  thf(redefinition_k1_relset_1, axiom,
% 9.27/9.51    (![A:$i,B:$i,C:$i]:
% 9.27/9.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.27/9.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.27/9.51  thf('14', plain,
% 9.27/9.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.27/9.51         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 9.27/9.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.27/9.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.27/9.51  thf('15', plain,
% 9.27/9.51      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 9.27/9.51         = (k1_relat_1 @ sk_B_1))),
% 9.27/9.51      inference('sup-', [status(thm)], ['13', '14'])).
% 9.27/9.51  thf('16', plain,
% 9.27/9.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.27/9.51         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 9.27/9.51          | (v1_funct_2 @ X30 @ X28 @ X29)
% 9.27/9.51          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 9.27/9.51  thf('17', plain,
% 9.27/9.51      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 9.27/9.51        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 9.27/9.51        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 9.27/9.51      inference('sup-', [status(thm)], ['15', '16'])).
% 9.27/9.51  thf('18', plain,
% 9.27/9.51      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 9.27/9.51        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 9.27/9.51      inference('simplify', [status(thm)], ['17'])).
% 9.27/9.51  thf('19', plain,
% 9.27/9.51      ((~ (v1_funct_1 @ sk_B_1)
% 9.27/9.51        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 9.27/9.51        | ~ (m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.27/9.51  thf('20', plain,
% 9.27/9.51      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 9.27/9.51         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 9.27/9.51      inference('split', [status(esa)], ['19'])).
% 9.27/9.51  thf('21', plain, ((v1_funct_1 @ sk_B_1)),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.27/9.51  thf('22', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 9.27/9.51      inference('split', [status(esa)], ['19'])).
% 9.27/9.51  thf('23', plain, (((v1_funct_1 @ sk_B_1))),
% 9.27/9.51      inference('sup-', [status(thm)], ['21', '22'])).
% 9.27/9.51  thf('24', plain,
% 9.27/9.51      ((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 9.27/9.51      inference('demod', [status(thm)], ['8', '9'])).
% 9.27/9.51  thf('25', plain,
% 9.27/9.51      ((~ (m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 9.27/9.51         <= (~
% 9.27/9.51             ((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 9.27/9.51      inference('split', [status(esa)], ['19'])).
% 9.27/9.51  thf('26', plain,
% 9.27/9.51      (((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 9.27/9.51      inference('sup-', [status(thm)], ['24', '25'])).
% 9.27/9.51  thf('27', plain,
% 9.27/9.51      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 9.27/9.51       ~
% 9.27/9.51       ((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 9.27/9.51       ~ ((v1_funct_1 @ sk_B_1))),
% 9.27/9.51      inference('split', [status(esa)], ['19'])).
% 9.27/9.51  thf('28', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 9.27/9.51      inference('sat_resolution*', [status(thm)], ['23', '26', '27'])).
% 9.27/9.51  thf('29', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 9.27/9.51      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 9.27/9.51  thf('30', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 9.27/9.51      inference('clc', [status(thm)], ['18', '29'])).
% 9.27/9.51  thf('31', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 9.27/9.51      inference('clc', [status(thm)], ['12', '30'])).
% 9.27/9.51  thf('32', plain,
% 9.27/9.51      ((~ (zip_tseitin_0 @ sk_A @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 9.27/9.51      inference('sup-', [status(thm)], ['2', '31'])).
% 9.27/9.51  thf('33', plain,
% 9.27/9.51      (![X26 : $i, X27 : $i]:
% 9.27/9.51         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 9.27/9.51  thf('34', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 9.27/9.51      inference('simplify', [status(thm)], ['33'])).
% 9.27/9.51  thf('35', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 9.27/9.51      inference('demod', [status(thm)], ['32', '34'])).
% 9.27/9.51  thf(d1_xboole_0, axiom,
% 9.27/9.51    (![A:$i]:
% 9.27/9.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 9.27/9.51  thf('36', plain,
% 9.27/9.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 9.27/9.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 9.27/9.51  thf('37', plain,
% 9.27/9.51      ((m1_subset_1 @ sk_B_1 @ 
% 9.27/9.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 9.27/9.51      inference('demod', [status(thm)], ['8', '9'])).
% 9.27/9.51  thf(t5_subset, axiom,
% 9.27/9.51    (![A:$i,B:$i,C:$i]:
% 9.27/9.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 9.27/9.51          ( v1_xboole_0 @ C ) ) ))).
% 9.27/9.51  thf('38', plain,
% 9.27/9.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.27/9.51         (~ (r2_hidden @ X13 @ X14)
% 9.27/9.51          | ~ (v1_xboole_0 @ X15)
% 9.27/9.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 9.27/9.51      inference('cnf', [status(esa)], [t5_subset])).
% 9.27/9.51  thf('39', plain,
% 9.27/9.51      (![X0 : $i]:
% 9.27/9.51         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 9.27/9.51          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 9.27/9.51      inference('sup-', [status(thm)], ['37', '38'])).
% 9.27/9.51  thf('40', plain,
% 9.27/9.51      (![X26 : $i, X27 : $i]:
% 9.27/9.51         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 9.27/9.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 9.27/9.51  thf('41', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 9.27/9.51      inference('clc', [status(thm)], ['12', '30'])).
% 9.27/9.51  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 9.27/9.51      inference('sup-', [status(thm)], ['40', '41'])).
% 9.27/9.51  thf(t113_zfmisc_1, axiom,
% 9.27/9.51    (![A:$i,B:$i]:
% 9.27/9.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.27/9.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.27/9.51  thf('43', plain,
% 9.27/9.51      (![X8 : $i, X9 : $i]:
% 9.27/9.51         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 9.27/9.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.27/9.51  thf('44', plain,
% 9.27/9.51      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 9.27/9.51      inference('simplify', [status(thm)], ['43'])).
% 9.27/9.51  thf(rc1_relset_1, axiom,
% 9.27/9.51    (![A:$i,B:$i]:
% 9.27/9.51     ( ?[C:$i]:
% 9.27/9.51       ( ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 9.27/9.51         ( v1_relat_1 @ C ) & ( v1_xboole_0 @ C ) & 
% 9.27/9.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 9.27/9.51  thf('45', plain, (![X34 : $i, X35 : $i]: (v1_xboole_0 @ (sk_C @ X34 @ X35))),
% 9.27/9.51      inference('cnf', [status(esa)], [rc1_relset_1])).
% 9.27/9.51  thf('46', plain, (![X34 : $i, X35 : $i]: (v1_xboole_0 @ (sk_C @ X34 @ X35))),
% 9.27/9.51      inference('cnf', [status(esa)], [rc1_relset_1])).
% 9.27/9.51  thf('47', plain,
% 9.27/9.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 9.27/9.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.27/9.51  thf('48', plain, (![X0 : $i, X1 : $i]: ((sk_C @ X1 @ X0) = (k1_xboole_0))),
% 9.27/9.51      inference('sup-', [status(thm)], ['46', '47'])).
% 9.27/9.51  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.27/9.51      inference('demod', [status(thm)], ['45', '48'])).
% 9.27/9.51  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 9.27/9.51      inference('demod', [status(thm)], ['39', '42', '44', '49'])).
% 9.27/9.51  thf('51', plain, ((v1_xboole_0 @ sk_B_1)),
% 9.27/9.51      inference('sup-', [status(thm)], ['36', '50'])).
% 9.27/9.51  thf('52', plain, ($false), inference('demod', [status(thm)], ['35', '51'])).
% 9.27/9.51  
% 9.27/9.51  % SZS output end Refutation
% 9.27/9.51  
% 9.27/9.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
