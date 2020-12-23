%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1TVi2AbuNX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:11 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 207 expanded)
%              Number of leaves         :   41 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  631 (2496 expanded)
%              Number of equality atoms :   48 ( 134 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('1',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) )
        = X10 )
      | ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 != X6 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X6 ) )
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X6 ) )
     != ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k11_relat_1 @ X22 @ X21 )
        = ( k1_tarski @ ( k1_funct_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ X14 @ ( k1_tarski @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('47',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','47'])).

thf('49',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1TVi2AbuNX
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:58:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.60  % Solved by: fo/fo7.sh
% 0.23/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.60  % done 119 iterations in 0.123s
% 0.23/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.60  % SZS output start Refutation
% 0.23/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.60  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.23/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.23/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.23/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.60  thf(t144_relat_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( v1_relat_1 @ B ) =>
% 0.23/0.60       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.23/0.60  thf('0', plain,
% 0.23/0.60      (![X18 : $i, X19 : $i]:
% 0.23/0.60         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 0.23/0.60          | ~ (v1_relat_1 @ X18))),
% 0.23/0.60      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.23/0.60  thf(t64_funct_2, conjecture,
% 0.23/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.60         ( m1_subset_1 @
% 0.23/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.60         ( r1_tarski @
% 0.23/0.60           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.23/0.60           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.23/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.60            ( m1_subset_1 @
% 0.23/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.60            ( r1_tarski @
% 0.23/0.60              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.23/0.60              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.23/0.60    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.23/0.60  thf('1', plain,
% 0.23/0.60      (~ (r1_tarski @ 
% 0.23/0.60          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.23/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('2', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf(d1_funct_2, axiom,
% 0.23/0.60    (![A:$i,B:$i,C:$i]:
% 0.23/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.23/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.23/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.23/0.60  thf(zf_stmt_1, axiom,
% 0.23/0.60    (![C:$i,B:$i,A:$i]:
% 0.23/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.23/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.23/0.60  thf('3', plain,
% 0.23/0.60      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.23/0.60         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.23/0.60          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.23/0.60          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.23/0.60  thf('4', plain,
% 0.23/0.60      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.23/0.60        | ((k1_tarski @ sk_A)
% 0.23/0.60            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.60  thf(zf_stmt_2, axiom,
% 0.23/0.60    (![B:$i,A:$i]:
% 0.23/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.23/0.60  thf('5', plain,
% 0.23/0.60      (![X30 : $i, X31 : $i]:
% 0.23/0.60         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.60  thf('6', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ 
% 0.23/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.23/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.23/0.60  thf(zf_stmt_5, axiom,
% 0.23/0.60    (![A:$i,B:$i,C:$i]:
% 0.23/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.23/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.23/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.23/0.60  thf('7', plain,
% 0.23/0.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.23/0.60         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.23/0.60          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.23/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.23/0.60  thf('8', plain,
% 0.23/0.60      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.23/0.60        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.60  thf('9', plain,
% 0.23/0.60      ((((sk_B) = (k1_xboole_0))
% 0.23/0.60        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['5', '8'])).
% 0.23/0.60  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('11', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.23/0.60      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.23/0.60  thf('12', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ 
% 0.23/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.60    (![A:$i,B:$i,C:$i]:
% 0.23/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.60  thf('13', plain,
% 0.23/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.60         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.23/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.23/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.60  thf('14', plain,
% 0.23/0.60      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.23/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.60  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.60      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.23/0.60  thf('16', plain,
% 0.23/0.60      (~ (r1_tarski @ 
% 0.23/0.60          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.23/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.60      inference('demod', [status(thm)], ['1', '15'])).
% 0.23/0.60  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.60      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.23/0.60  thf(t65_zfmisc_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.23/0.60       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.23/0.60  thf('18', plain,
% 0.23/0.60      (![X10 : $i, X11 : $i]:
% 0.23/0.60         (((k4_xboole_0 @ X10 @ (k1_tarski @ X11)) = (X10))
% 0.23/0.60          | (r2_hidden @ X11 @ X10))),
% 0.23/0.60      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.23/0.60  thf(t20_zfmisc_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.23/0.60         ( k1_tarski @ A ) ) <=>
% 0.23/0.60       ( ( A ) != ( B ) ) ))).
% 0.23/0.60  thf('19', plain,
% 0.23/0.60      (![X6 : $i, X7 : $i]:
% 0.23/0.60         (((X7) != (X6))
% 0.23/0.60          | ((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X6))
% 0.23/0.60              != (k1_tarski @ X7)))),
% 0.23/0.60      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.23/0.60  thf('20', plain,
% 0.23/0.60      (![X6 : $i]:
% 0.23/0.60         ((k4_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X6))
% 0.23/0.60           != (k1_tarski @ X6))),
% 0.23/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.23/0.60  thf('21', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.23/0.60          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['18', '20'])).
% 0.23/0.60  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.60  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.23/0.60      inference('sup+', [status(thm)], ['17', '22'])).
% 0.23/0.60  thf(t117_funct_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.60       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.60         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.23/0.60  thf('24', plain,
% 0.23/0.60      (![X21 : $i, X22 : $i]:
% 0.23/0.60         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.23/0.60          | ((k11_relat_1 @ X22 @ X21) = (k1_tarski @ (k1_funct_1 @ X22 @ X21)))
% 0.23/0.60          | ~ (v1_funct_1 @ X22)
% 0.23/0.60          | ~ (v1_relat_1 @ X22))),
% 0.23/0.60      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.23/0.60  thf('25', plain,
% 0.23/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.23/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.23/0.60        | ((k11_relat_1 @ sk_D @ sk_A)
% 0.23/0.60            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.60  thf('26', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ 
% 0.23/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf(cc2_relat_1, axiom,
% 0.23/0.60    (![A:$i]:
% 0.23/0.60     ( ( v1_relat_1 @ A ) =>
% 0.23/0.60       ( ![B:$i]:
% 0.23/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.60  thf('27', plain,
% 0.23/0.60      (![X12 : $i, X13 : $i]:
% 0.23/0.60         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.23/0.60          | (v1_relat_1 @ X12)
% 0.23/0.60          | ~ (v1_relat_1 @ X13))),
% 0.23/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.60  thf('28', plain,
% 0.23/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.23/0.60        | (v1_relat_1 @ sk_D))),
% 0.23/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.60  thf(fc6_relat_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.60  thf('29', plain,
% 0.23/0.60      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.23/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.60  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.60  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('32', plain,
% 0.23/0.60      (((k11_relat_1 @ sk_D @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.60      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.23/0.60  thf('33', plain,
% 0.23/0.60      (~ (r1_tarski @ 
% 0.23/0.60          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.23/0.60          (k11_relat_1 @ sk_D @ sk_A))),
% 0.23/0.60      inference('demod', [status(thm)], ['16', '32'])).
% 0.23/0.60  thf('34', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ 
% 0.23/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.60      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.23/0.60  thf('36', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ 
% 0.23/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.23/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.23/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.23/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.23/0.60  thf('37', plain,
% 0.23/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.23/0.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.23/0.60          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.23/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.23/0.60  thf('38', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.23/0.60           = (k9_relat_1 @ sk_D @ X0))),
% 0.23/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.60  thf('39', plain,
% 0.23/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k11_relat_1 @ sk_D @ sk_A))),
% 0.23/0.60      inference('demod', [status(thm)], ['33', '38'])).
% 0.23/0.60  thf(t146_relat_1, axiom,
% 0.23/0.60    (![A:$i]:
% 0.23/0.60     ( ( v1_relat_1 @ A ) =>
% 0.23/0.60       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.23/0.60  thf('40', plain,
% 0.23/0.60      (![X20 : $i]:
% 0.23/0.60         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 0.23/0.60          | ~ (v1_relat_1 @ X20))),
% 0.23/0.60      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.23/0.60  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.60      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.23/0.60  thf(d16_relat_1, axiom,
% 0.23/0.60    (![A:$i]:
% 0.23/0.60     ( ( v1_relat_1 @ A ) =>
% 0.23/0.60       ( ![B:$i]:
% 0.23/0.60         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.23/0.60  thf('42', plain,
% 0.23/0.60      (![X14 : $i, X15 : $i]:
% 0.23/0.60         (((k11_relat_1 @ X14 @ X15) = (k9_relat_1 @ X14 @ (k1_tarski @ X15)))
% 0.23/0.60          | ~ (v1_relat_1 @ X14))),
% 0.23/0.60      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.23/0.60  thf('43', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D)))
% 0.23/0.60          | ~ (v1_relat_1 @ X0))),
% 0.23/0.60      inference('sup+', [status(thm)], ['41', '42'])).
% 0.23/0.60  thf('44', plain,
% 0.23/0.60      ((((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))
% 0.23/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.23/0.60        | ~ (v1_relat_1 @ sk_D))),
% 0.23/0.60      inference('sup+', [status(thm)], ['40', '43'])).
% 0.23/0.60  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.60  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.60  thf('47', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 0.23/0.60      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.23/0.60  thf('48', plain,
% 0.23/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.23/0.60      inference('demod', [status(thm)], ['39', '47'])).
% 0.23/0.60  thf('49', plain, (~ (v1_relat_1 @ sk_D)),
% 0.23/0.60      inference('sup-', [status(thm)], ['0', '48'])).
% 0.23/0.60  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.60  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.23/0.60  
% 0.23/0.60  % SZS output end Refutation
% 0.23/0.60  
% 0.23/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
