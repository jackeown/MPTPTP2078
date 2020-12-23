%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yMuaOEA2lO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:40 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 389 expanded)
%              Number of leaves         :   29 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  694 (4126 expanded)
%              Number of equality atoms :   45 ( 106 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','16','17'])).

thf('19',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

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

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

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

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    ! [X32: $i] :
      ( zip_tseitin_0 @ X32 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['52','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['19','40','41','42','43','44','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yMuaOEA2lO
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.67  % Solved by: fo/fo7.sh
% 0.44/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.67  % done 228 iterations in 0.200s
% 0.44/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.67  % SZS output start Refutation
% 0.44/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.67  thf(t3_funct_2, conjecture,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.67       ( ( v1_funct_1 @ A ) & 
% 0.44/0.67         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.44/0.67         ( m1_subset_1 @
% 0.44/0.67           A @ 
% 0.44/0.67           ( k1_zfmisc_1 @
% 0.44/0.67             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.67    (~( ![A:$i]:
% 0.44/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.67          ( ( v1_funct_1 @ A ) & 
% 0.44/0.67            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.44/0.67            ( m1_subset_1 @
% 0.44/0.67              A @ 
% 0.44/0.67              ( k1_zfmisc_1 @
% 0.44/0.67                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.44/0.67    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.44/0.67  thf('0', plain,
% 0.44/0.67      ((~ (v1_funct_1 @ sk_A)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.44/0.67        | ~ (m1_subset_1 @ sk_A @ 
% 0.44/0.67             (k1_zfmisc_1 @ 
% 0.44/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('1', plain,
% 0.44/0.67      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.44/0.67         <= (~
% 0.44/0.67             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.44/0.67      inference('split', [status(esa)], ['0'])).
% 0.44/0.67  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.44/0.67      inference('split', [status(esa)], ['0'])).
% 0.44/0.67  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.67  thf(d3_tarski, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.67  thf('5', plain,
% 0.44/0.67      (![X4 : $i, X6 : $i]:
% 0.44/0.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.44/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.67  thf('6', plain,
% 0.44/0.67      (![X4 : $i, X6 : $i]:
% 0.44/0.67         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.44/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.67  thf('7', plain,
% 0.44/0.67      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.67  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.67      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.67  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.67      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.67  thf(t11_relset_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ C ) =>
% 0.44/0.67       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.44/0.67           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.44/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.44/0.67  thf('10', plain,
% 0.44/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.67         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.44/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 0.44/0.67          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.44/0.67          | ~ (v1_relat_1 @ X29))),
% 0.44/0.67      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.44/0.67  thf('11', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X0)
% 0.44/0.67          | (m1_subset_1 @ X0 @ 
% 0.44/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.44/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.67  thf('12', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((m1_subset_1 @ X0 @ 
% 0.44/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['8', '11'])).
% 0.44/0.67  thf('13', plain,
% 0.44/0.67      ((~ (m1_subset_1 @ sk_A @ 
% 0.44/0.67           (k1_zfmisc_1 @ 
% 0.44/0.67            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.44/0.67         <= (~
% 0.44/0.67             ((m1_subset_1 @ sk_A @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.44/0.67      inference('split', [status(esa)], ['0'])).
% 0.44/0.67  thf('14', plain,
% 0.44/0.67      ((~ (v1_relat_1 @ sk_A))
% 0.44/0.67         <= (~
% 0.44/0.67             ((m1_subset_1 @ sk_A @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('16', plain,
% 0.44/0.67      (((m1_subset_1 @ sk_A @ 
% 0.44/0.67         (k1_zfmisc_1 @ 
% 0.44/0.67          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.44/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.67  thf('17', plain,
% 0.44/0.67      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.44/0.67       ~
% 0.44/0.67       ((m1_subset_1 @ sk_A @ 
% 0.44/0.67         (k1_zfmisc_1 @ 
% 0.44/0.67          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.44/0.67       ~ ((v1_funct_1 @ sk_A))),
% 0.44/0.67      inference('split', [status(esa)], ['0'])).
% 0.44/0.67  thf('18', plain,
% 0.44/0.67      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.44/0.67      inference('sat_resolution*', [status(thm)], ['4', '16', '17'])).
% 0.44/0.67  thf('19', plain,
% 0.44/0.67      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.44/0.67      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.44/0.67  thf(d1_funct_2, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_1, axiom,
% 0.44/0.67    (![B:$i,A:$i]:
% 0.44/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.67  thf('20', plain,
% 0.44/0.67      (![X32 : $i, X33 : $i]:
% 0.44/0.67         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.67  thf(t64_relat_1, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ A ) =>
% 0.44/0.67       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.67           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.67         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.67  thf('21', plain,
% 0.44/0.67      (![X20 : $i]:
% 0.44/0.67         (((k2_relat_1 @ X20) != (k1_xboole_0))
% 0.44/0.67          | ((X20) = (k1_xboole_0))
% 0.44/0.67          | ~ (v1_relat_1 @ X20))),
% 0.44/0.67      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.44/0.67  thf('22', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (((k2_relat_1 @ X1) != (X0))
% 0.44/0.67          | (zip_tseitin_0 @ X0 @ X2)
% 0.44/0.67          | ~ (v1_relat_1 @ X1)
% 0.44/0.67          | ((X1) = (k1_xboole_0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      (![X1 : $i, X2 : $i]:
% 0.44/0.67         (((X1) = (k1_xboole_0))
% 0.44/0.67          | ~ (v1_relat_1 @ X1)
% 0.44/0.67          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 0.44/0.67      inference('simplify', [status(thm)], ['22'])).
% 0.44/0.67  thf('24', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((m1_subset_1 @ X0 @ 
% 0.44/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['8', '11'])).
% 0.44/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.67  thf(zf_stmt_3, axiom,
% 0.44/0.67    (![C:$i,B:$i,A:$i]:
% 0.44/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.67  thf(zf_stmt_5, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.67  thf('25', plain,
% 0.44/0.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.67         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.44/0.67          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.44/0.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X0)
% 0.44/0.67          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.44/0.67          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.67  thf('27', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X0)
% 0.44/0.67          | ((X0) = (k1_xboole_0))
% 0.44/0.67          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['23', '26'])).
% 0.44/0.67  thf('28', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.44/0.67          | ((X0) = (k1_xboole_0))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('simplify', [status(thm)], ['27'])).
% 0.44/0.67  thf('29', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((m1_subset_1 @ X0 @ 
% 0.44/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['8', '11'])).
% 0.44/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.67  thf('30', plain,
% 0.44/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.67         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.44/0.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.44/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X0)
% 0.44/0.67          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.44/0.67              = (k1_relat_1 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.67  thf('32', plain,
% 0.44/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.67         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.44/0.67          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.44/0.67          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ X0)
% 0.44/0.67          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.44/0.67          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.67  thf('34', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.44/0.67          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('simplify', [status(thm)], ['33'])).
% 0.44/0.67  thf('35', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (v1_relat_1 @ X0)
% 0.44/0.67          | ((X0) = (k1_xboole_0))
% 0.44/0.67          | ~ (v1_relat_1 @ X0)
% 0.44/0.67          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['28', '34'])).
% 0.44/0.67  thf('36', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.44/0.67          | ((X0) = (k1_xboole_0))
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('simplify', [status(thm)], ['35'])).
% 0.44/0.67  thf('37', plain,
% 0.44/0.67      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.44/0.67      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.44/0.67  thf('38', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.67  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.67  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.67  thf(t60_relat_1, axiom,
% 0.44/0.67    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.44/0.67     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.67  thf('42', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.67  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.67  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.67  thf(t4_subset_1, axiom,
% 0.44/0.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.67  thf('45', plain,
% 0.44/0.67      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.67  thf('46', plain,
% 0.44/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.67         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.44/0.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.44/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.67  thf('47', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.67  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.67  thf('49', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('demod', [status(thm)], ['47', '48'])).
% 0.44/0.67  thf('50', plain,
% 0.44/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.67         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.44/0.67          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.44/0.67          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.67  thf('51', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((X1) != (k1_xboole_0))
% 0.44/0.67          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.44/0.67          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.67  thf('52', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.44/0.67          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('simplify', [status(thm)], ['51'])).
% 0.44/0.67  thf('53', plain,
% 0.44/0.67      (![X32 : $i, X33 : $i]:
% 0.44/0.67         ((zip_tseitin_0 @ X32 @ X33) | ((X33) != (k1_xboole_0)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.67  thf('54', plain, (![X32 : $i]: (zip_tseitin_0 @ X32 @ k1_xboole_0)),
% 0.44/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.44/0.67  thf('55', plain,
% 0.44/0.67      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.44/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.67  thf('56', plain,
% 0.44/0.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.67         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.44/0.67          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.44/0.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.67  thf('57', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.44/0.67  thf('58', plain,
% 0.44/0.67      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.44/0.68      inference('sup-', [status(thm)], ['54', '57'])).
% 0.44/0.68  thf('59', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.68      inference('demod', [status(thm)], ['52', '58'])).
% 0.44/0.68  thf('60', plain, ($false),
% 0.44/0.68      inference('demod', [status(thm)],
% 0.44/0.68                ['19', '40', '41', '42', '43', '44', '59'])).
% 0.44/0.68  
% 0.44/0.68  % SZS output end Refutation
% 0.44/0.68  
% 0.44/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
