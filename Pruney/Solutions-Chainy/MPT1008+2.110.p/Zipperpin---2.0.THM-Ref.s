%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zbtKBbJ6wE

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 210 expanded)
%              Number of leaves         :   39 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  679 (2416 expanded)
%              Number of equality atoms :   79 ( 198 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X10 ) @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k11_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k11_relat_1 @ X25 @ X24 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('40',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38','39','40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('50',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','48','50'])).

thf('52',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zbtKBbJ6wE
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 175 iterations in 0.137s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(t62_funct_2, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.58         ( m1_subset_1 @
% 0.20/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.58       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.58         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.58           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.58            ( m1_subset_1 @
% 0.20/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.58          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.58            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.58              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.58  thf('0', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(d1_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_1, axiom,
% 0.20/0.58    (![C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.58         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.20/0.58          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.20/0.58          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.58        | ((k1_tarski @ sk_A)
% 0.20/0.58            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf(zf_stmt_2, axiom,
% 0.20/0.58    (![B:$i,A:$i]:
% 0.20/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X32 : $i, X33 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_5, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.20/0.58          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.20/0.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.58        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      ((((sk_B) = (k1_xboole_0))
% 0.20/0.58        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.58  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.20/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.20/0.58  thf(t130_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.58       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i]:
% 0.20/0.58         (((X9) = (k1_xboole_0))
% 0.20/0.58          | ((k2_zfmisc_1 @ (k1_tarski @ X10) @ X9) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0) != (k1_xboole_0))
% 0.20/0.58          | ((X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.58  thf(t205_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ B ) =>
% 0.20/0.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.58         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         (((k11_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.20/0.58          | (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.20/0.58          | ~ (v1_relat_1 @ X21))),
% 0.20/0.58      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.20/0.58  thf(t117_funct_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.58         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X24 : $i, X25 : $i]:
% 0.20/0.58         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.20/0.58          | ((k11_relat_1 @ X25 @ X24) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.20/0.58          | ~ (v1_funct_1 @ X25)
% 0.20/0.58          | ~ (v1_relat_1 @ X25))),
% 0.20/0.58      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_funct_1 @ X0)
% 0.20/0.58          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0)
% 0.20/0.58          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.20/0.58         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.20/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.58      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      ((((k2_relat_1 @ sk_C) != (k11_relat_1 @ sk_C @ sk_A))
% 0.20/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.58        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.20/0.58        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['20', '25'])).
% 0.20/0.58  thf(t146_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 0.20/0.58          | ~ (v1_relat_1 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.58  thf('28', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.20/0.58  thf(d16_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X16 : $i, X17 : $i]:
% 0.20/0.58         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.20/0.58          | ~ (v1_relat_1 @ X16))),
% 0.20/0.58      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C)))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      ((((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.20/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup+', [status(thm)], ['27', '30'])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc2_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.20/0.58          | (v1_relat_1 @ X14)
% 0.20/0.58          | ~ (v1_relat_1 @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.58        | (v1_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.58  thf(fc6_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.58  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('38', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.20/0.58  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('40', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.20/0.58  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.20/0.58        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '38', '39', '40', '41'])).
% 0.20/0.58  thf('43', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.58  thf(t65_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.58         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (![X23 : $i]:
% 0.20/0.58         (((k2_relat_1 @ X23) != (k1_xboole_0))
% 0.20/0.58          | ((k1_relat_1 @ X23) = (k1_xboole_0))
% 0.20/0.58          | ~ (v1_relat_1 @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.58  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.58  thf('48', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.58  thf(t113_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['16', '48', '50'])).
% 0.20/0.58  thf('52', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.58  thf('53', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['0', '52'])).
% 0.20/0.58  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
