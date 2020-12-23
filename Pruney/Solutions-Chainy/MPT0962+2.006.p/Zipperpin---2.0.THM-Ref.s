%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NwssOJsSRY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 227 expanded)
%              Number of leaves         :   35 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  592 (2447 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X25: $i] :
      ( zip_tseitin_0 @ X25 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X20 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('30',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['30','33','34'])).

thf('36',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['27','35'])).

thf('37',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','36'])).

thf('38',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['19','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','38'])).

thf('40',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['19','37'])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','46','48','49'])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['39','51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NwssOJsSRY
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 324 iterations in 0.288s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.73  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.73  thf(t29_mcart_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.73          ( ![B:$i]:
% 0.52/0.73            ( ~( ( r2_hidden @ B @ A ) & 
% 0.52/0.73                 ( ![C:$i,D:$i,E:$i]:
% 0.52/0.73                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.52/0.73                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (![X21 : $i]:
% 0.52/0.73         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 0.52/0.73      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.52/0.73  thf(d10_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.73  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.73      inference('simplify', [status(thm)], ['1'])).
% 0.52/0.73  thf(t3_subset, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X6 : $i, X8 : $i]:
% 0.52/0.73         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.73  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.73  thf(t5_subset, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.52/0.73          ( v1_xboole_0 @ C ) ) ))).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X9 @ X10)
% 0.52/0.73          | ~ (v1_xboole_0 @ X11)
% 0.52/0.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t5_subset])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['0', '6'])).
% 0.52/0.73  thf(d1_funct_2, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, axiom,
% 0.52/0.73    (![B:$i,A:$i]:
% 0.52/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X25 : $i, X26 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X25 @ X26) | ((X26) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('9', plain, (![X25 : $i]: (zip_tseitin_0 @ X25 @ k1_xboole_0)),
% 0.52/0.73      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['7', '9'])).
% 0.52/0.73  thf(t4_funct_2, conjecture,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.73       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.52/0.73         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.52/0.73           ( m1_subset_1 @
% 0.52/0.73             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_1, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i]:
% 0.52/0.73        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.73          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.52/0.73            ( ( v1_funct_1 @ B ) & 
% 0.52/0.73              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.52/0.73              ( m1_subset_1 @
% 0.52/0.73                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.52/0.73  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.73      inference('simplify', [status(thm)], ['1'])).
% 0.52/0.73  thf(t11_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ C ) =>
% 0.52/0.73       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.52/0.73           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.52/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.52/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X18) @ X20)
% 0.52/0.73          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.52/0.73          | ~ (v1_relat_1 @ X18))),
% 0.52/0.73      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X0)
% 0.52/0.73          | (m1_subset_1 @ X0 @ 
% 0.52/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.52/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.52/0.73        | ~ (v1_relat_1 @ sk_B_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['11', '14'])).
% 0.52/0.73  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_3, axiom,
% 0.52/0.73    (![C:$i,B:$i,A:$i]:
% 0.52/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_5, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.73         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.52/0.73          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.52/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.52/0.73        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.52/0.73          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.52/0.73         = (k1_relat_1 @ sk_B_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.73         (((X27) != (k1_relset_1 @ X27 @ X28 @ X29))
% 0.52/0.73          | (v1_funct_2 @ X29 @ X27 @ X28)
% 0.52/0.73          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.52/0.73        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.52/0.73        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.52/0.73        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['24'])).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.52/0.73        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.52/0.73         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.52/0.73      inference('split', [status(esa)], ['26'])).
% 0.52/0.73  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('29', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.52/0.73      inference('split', [status(esa)], ['26'])).
% 0.52/0.73  thf('30', plain, (((v1_funct_1 @ sk_B_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.52/0.73         <= (~
% 0.52/0.73             ((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.52/0.73      inference('split', [status(esa)], ['26'])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.52/0.73       ~
% 0.52/0.73       ((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.52/0.73       ~ ((v1_funct_1 @ sk_B_1))),
% 0.52/0.73      inference('split', [status(esa)], ['26'])).
% 0.52/0.73  thf('35', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.52/0.73      inference('sat_resolution*', [status(thm)], ['30', '33', '34'])).
% 0.52/0.73  thf('36', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.52/0.73      inference('simpl_trail', [status(thm)], ['27', '35'])).
% 0.52/0.73  thf('37', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.52/0.73      inference('clc', [status(thm)], ['25', '36'])).
% 0.52/0.73  thf('38', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.52/0.73      inference('clc', [status(thm)], ['19', '37'])).
% 0.52/0.73  thf('39', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_B_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['10', '38'])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X21 : $i]:
% 0.52/0.73         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 0.52/0.73      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X9 @ X10)
% 0.52/0.73          | ~ (v1_xboole_0 @ X11)
% 0.52/0.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t5_subset])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.52/0.73          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X25 : $i, X26 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('45', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.52/0.73      inference('clc', [status(thm)], ['19', '37'])).
% 0.52/0.73  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.73  thf(t113_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['47'])).
% 0.52/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.73  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.73  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.52/0.73      inference('demod', [status(thm)], ['43', '46', '48', '49'])).
% 0.52/0.73  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['40', '50'])).
% 0.52/0.73  thf(t60_relat_1, axiom,
% 0.52/0.73    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.73     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.73  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.73  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.73  thf('54', plain, ($false),
% 0.52/0.73      inference('demod', [status(thm)], ['39', '51', '52', '53'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
