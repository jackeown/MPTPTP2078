%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eDoSzgrM9j

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:13 EST 2020

% Result     : Theorem 15.27s
% Output     : Refutation 15.27s
% Verified   : 
% Statistics : Number of formulae       :  245 (1057 expanded)
%              Number of leaves         :   38 ( 325 expanded)
%              Depth                    :   27
%              Number of atoms          : 2470 (17369 expanded)
%              Number of equality atoms :  220 (1263 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t145_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( A = k1_xboole_0 ) )
           => ( ( r1_partfun1 @ C @ D )
            <=> ! [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( A = k1_xboole_0 ) )
             => ( ( r1_partfun1 @ C @ D )
              <=> ! [E: $i] :
                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                   => ( ( k1_funct_1 @ C @ E )
                      = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_funct_2])).

thf('0',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = ( k1_funct_1 @ sk_D @ X27 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,
    ( ( v4_relat_1 @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ k1_xboole_0 )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( r1_partfun1 @ X25 @ X24 )
      | ( ( k1_funct_1 @ X25 @ X26 )
        = ( k1_funct_1 @ X24 @ X26 ) )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X1 )
          = ( k1_funct_1 @ X0 @ X1 ) )
        | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('36',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_1 @ X1 )
          = ( k1_funct_1 @ X0 @ X1 ) )
        | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
        | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
          = ( k1_funct_1 @ X0 @ sk_E ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
        = ( k1_funct_1 @ sk_D @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_1 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_1 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','44'])).

thf('46',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_1 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('59',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ ( k1_relat_1 @ X25 ) )
      | ( r1_partfun1 @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('72',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('74',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = ( k1_funct_1 @ sk_D @ X27 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = ( k1_funct_1 @ sk_D @ X27 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r1_partfun1 @ sk_C_1 @ sk_D )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_funct_1 @ X25 @ ( sk_C @ X24 @ X25 ) )
       != ( k1_funct_1 @ X24 @ ( sk_C @ X24 @ X25 ) ) )
      | ( r1_partfun1 @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('83',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('85',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('87',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('88',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('91',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88','89','90'])).

thf('92',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('94',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('101',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

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

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('104',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('108',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('115',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('119',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('123',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ k1_xboole_0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','124'])).

thf('126',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['125'])).

thf('127',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('128',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('130',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ ( k1_relat_1 @ X25 ) )
      | ( r1_partfun1 @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('135',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('139',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('141',plain,
    ( ! [X27: $i] :
        ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X27 )
          = ( k1_funct_1 @ sk_D @ X27 ) ) )
   <= ! [X27: $i] :
        ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X27 )
          = ( k1_funct_1 @ sk_D @ X27 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X27: $i] :
        ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X27 )
          = ( k1_funct_1 @ sk_D @ X27 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_funct_1 @ X25 @ ( sk_C @ X24 @ X25 ) )
       != ( k1_funct_1 @ X24 @ ( sk_C @ X24 @ X25 ) ) )
      | ( r1_partfun1 @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('145',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('147',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('149',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('150',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('152',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149','150','151'])).

thf('153',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('155',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('157',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('158',plain,
    ( ! [X27: $i] :
        ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X27 )
          = ( k1_funct_1 @ sk_D @ X27 ) ) )
   <= ! [X27: $i] :
        ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X27 )
          = ( k1_funct_1 @ sk_D @ X27 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('159',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['46'])).

thf('161',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X27 )
            = ( k1_funct_1 @ sk_D @ X27 ) ) )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ! [X27: $i] :
        ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X27 )
          = ( k1_funct_1 @ sk_D @ X27 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('164',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('165',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('166',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('167',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('169',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = ( k1_funct_1 @ sk_D @ X27 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('170',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_funct_1 @ X25 @ ( sk_C @ X24 @ X25 ) )
       != ( k1_funct_1 @ X24 @ ( sk_C @ X24 @ X25 ) ) )
      | ( r1_partfun1 @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('173',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('175',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('177',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('178',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('180',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['173','174','175','176','177','178','179'])).

thf('181',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('183',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('184',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('185',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('187',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( r1_partfun1 @ X25 @ X24 )
      | ( ( k1_funct_1 @ X25 @ X26 )
        = ( k1_funct_1 @ X24 @ X26 ) )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['182','192'])).

thf('194',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['181','196'])).

thf('198',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('199',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['167','199'])).

thf('201',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['46'])).

thf('202',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( sk_B != k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('205',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['49','94','155','156','162','163','164','203','204'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eDoSzgrM9j
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 15.27/15.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.27/15.45  % Solved by: fo/fo7.sh
% 15.27/15.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.27/15.45  % done 6102 iterations in 14.993s
% 15.27/15.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.27/15.45  % SZS output start Refutation
% 15.27/15.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.27/15.45  thf(sk_B_type, type, sk_B: $i).
% 15.27/15.45  thf(sk_D_type, type, sk_D: $i).
% 15.27/15.45  thf(sk_A_type, type, sk_A: $i).
% 15.27/15.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.27/15.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.27/15.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.27/15.45  thf(sk_E_type, type, sk_E: $i).
% 15.27/15.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 15.27/15.45  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 15.27/15.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.27/15.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.27/15.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.27/15.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.27/15.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.27/15.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.27/15.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 15.27/15.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.27/15.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.27/15.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.27/15.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.27/15.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.27/15.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.27/15.45  thf(t145_funct_2, conjecture,
% 15.27/15.45    (![A:$i,B:$i,C:$i]:
% 15.27/15.45     ( ( ( v1_funct_1 @ C ) & 
% 15.27/15.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.27/15.45       ( ![D:$i]:
% 15.27/15.45         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.27/15.45             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.27/15.45           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.27/15.45             ( ( r1_partfun1 @ C @ D ) <=>
% 15.27/15.45               ( ![E:$i]:
% 15.27/15.45                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 15.27/15.45                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 15.27/15.45  thf(zf_stmt_0, negated_conjecture,
% 15.27/15.45    (~( ![A:$i,B:$i,C:$i]:
% 15.27/15.45        ( ( ( v1_funct_1 @ C ) & 
% 15.27/15.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.27/15.45          ( ![D:$i]:
% 15.27/15.45            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.27/15.45                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.27/15.45              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.27/15.45                ( ( r1_partfun1 @ C @ D ) <=>
% 15.27/15.45                  ( ![E:$i]:
% 15.27/15.45                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 15.27/15.45                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 15.27/15.45    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 15.27/15.45  thf('0', plain,
% 15.27/15.45      (![X27 : $i]:
% 15.27/15.45         (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45          | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))
% 15.27/15.45          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('1', plain,
% 15.27/15.45      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= (((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 15.27/15.45      inference('split', [status(esa)], ['0'])).
% 15.27/15.45  thf('2', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('3', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('split', [status(esa)], ['2'])).
% 15.27/15.45  thf('4', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('5', plain,
% 15.27/15.45      (((m1_subset_1 @ sk_C_1 @ 
% 15.27/15.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['3', '4'])).
% 15.27/15.45  thf(redefinition_k1_relset_1, axiom,
% 15.27/15.45    (![A:$i,B:$i,C:$i]:
% 15.27/15.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.27/15.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.27/15.45  thf('6', plain,
% 15.27/15.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 15.27/15.45         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 15.27/15.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 15.27/15.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.27/15.45  thf('7', plain,
% 15.27/15.45      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['5', '6'])).
% 15.27/15.45  thf('8', plain,
% 15.27/15.45      (((m1_subset_1 @ sk_C_1 @ 
% 15.27/15.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['3', '4'])).
% 15.27/15.45  thf(cc2_relset_1, axiom,
% 15.27/15.45    (![A:$i,B:$i,C:$i]:
% 15.27/15.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.27/15.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.27/15.45  thf('9', plain,
% 15.27/15.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.27/15.45         ((v4_relat_1 @ X10 @ X11)
% 15.27/15.45          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 15.27/15.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.27/15.45  thf('10', plain,
% 15.27/15.45      (((v4_relat_1 @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['8', '9'])).
% 15.27/15.45  thf(d18_relat_1, axiom,
% 15.27/15.45    (![A:$i,B:$i]:
% 15.27/15.45     ( ( v1_relat_1 @ B ) =>
% 15.27/15.45       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 15.27/15.45  thf('11', plain,
% 15.27/15.45      (![X6 : $i, X7 : $i]:
% 15.27/15.45         (~ (v4_relat_1 @ X6 @ X7)
% 15.27/15.45          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 15.27/15.45          | ~ (v1_relat_1 @ X6))),
% 15.27/15.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 15.27/15.45  thf('12', plain,
% 15.27/15.45      (((~ (v1_relat_1 @ sk_C_1)
% 15.27/15.45         | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['10', '11'])).
% 15.27/15.45  thf('13', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf(cc2_relat_1, axiom,
% 15.27/15.45    (![A:$i]:
% 15.27/15.45     ( ( v1_relat_1 @ A ) =>
% 15.27/15.45       ( ![B:$i]:
% 15.27/15.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 15.27/15.45  thf('14', plain,
% 15.27/15.45      (![X4 : $i, X5 : $i]:
% 15.27/15.45         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 15.27/15.45          | (v1_relat_1 @ X4)
% 15.27/15.45          | ~ (v1_relat_1 @ X5))),
% 15.27/15.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 15.27/15.45  thf('15', plain,
% 15.27/15.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 15.27/15.45      inference('sup-', [status(thm)], ['13', '14'])).
% 15.27/15.45  thf(fc6_relat_1, axiom,
% 15.27/15.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 15.27/15.45  thf('16', plain,
% 15.27/15.45      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 15.27/15.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 15.27/15.45  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('18', plain,
% 15.27/15.45      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['12', '17'])).
% 15.27/15.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.27/15.45  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.27/15.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.27/15.45  thf(d10_xboole_0, axiom,
% 15.27/15.45    (![A:$i,B:$i]:
% 15.27/15.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.27/15.45  thf('20', plain,
% 15.27/15.45      (![X0 : $i, X2 : $i]:
% 15.27/15.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.27/15.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.27/15.45  thf('21', plain,
% 15.27/15.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['19', '20'])).
% 15.27/15.45  thf('22', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf('23', plain,
% 15.27/15.45      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['7', '22'])).
% 15.27/15.45  thf('24', plain,
% 15.27/15.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('split', [status(esa)], ['2'])).
% 15.27/15.45  thf('25', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('26', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 15.27/15.45         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('split', [status(esa)], ['25'])).
% 15.27/15.45  thf('27', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['24', '26'])).
% 15.27/15.45  thf('28', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ k1_xboole_0))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['23', '27'])).
% 15.27/15.45  thf('29', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf(t132_partfun1, axiom,
% 15.27/15.45    (![A:$i]:
% 15.27/15.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.27/15.45       ( ![B:$i]:
% 15.27/15.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.27/15.45           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 15.27/15.45             ( ( r1_partfun1 @ A @ B ) <=>
% 15.27/15.45               ( ![C:$i]:
% 15.27/15.45                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 15.27/15.45                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 15.27/15.45  thf('30', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | ~ (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ((k1_funct_1 @ X25 @ X26) = (k1_funct_1 @ X24 @ X26))
% 15.27/15.45          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X25))
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('31', plain,
% 15.27/15.45      ((![X0 : $i, X1 : $i]:
% 15.27/15.45          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 15.27/15.45           | ~ (v1_relat_1 @ sk_C_1)
% 15.27/15.45           | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X1) = (k1_funct_1 @ X0 @ X1))
% 15.27/15.45           | ~ (r1_partfun1 @ sk_C_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | ~ (v1_relat_1 @ X0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['29', '30'])).
% 15.27/15.45  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.27/15.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.27/15.45  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('35', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf('36', plain,
% 15.27/15.45      ((![X0 : $i, X1 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X1 @ k1_xboole_0)
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X1) = (k1_funct_1 @ X0 @ X1))
% 15.27/15.45           | ~ (r1_partfun1 @ sk_C_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | ~ (v1_relat_1 @ X0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 15.27/15.45  thf('37', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (v1_relat_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | ~ (r1_partfun1 @ sk_C_1 @ X0)
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ X0 @ sk_E))))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['28', '36'])).
% 15.27/15.45  thf('38', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))
% 15.27/15.45         | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_D)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))) & 
% 15.27/15.45             ((r1_partfun1 @ sk_C_1 @ sk_D)) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['1', '37'])).
% 15.27/15.45  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('40', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('41', plain,
% 15.27/15.45      (![X4 : $i, X5 : $i]:
% 15.27/15.45         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 15.27/15.45          | (v1_relat_1 @ X4)
% 15.27/15.45          | ~ (v1_relat_1 @ X5))),
% 15.27/15.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 15.27/15.45  thf('42', plain,
% 15.27/15.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 15.27/15.45      inference('sup-', [status(thm)], ['40', '41'])).
% 15.27/15.45  thf('43', plain,
% 15.27/15.45      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 15.27/15.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 15.27/15.45  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('45', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))) & 
% 15.27/15.45             ((r1_partfun1 @ sk_C_1 @ sk_D)) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('demod', [status(thm)], ['38', '39', '44'])).
% 15.27/15.45  thf('46', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 15.27/15.45        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('47', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 15.27/15.45      inference('split', [status(esa)], ['46'])).
% 15.27/15.45  thf('48', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 15.27/15.45             (((sk_A) = (k1_xboole_0))) & 
% 15.27/15.45             ((r1_partfun1 @ sk_C_1 @ sk_D)) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['45', '47'])).
% 15.27/15.45  thf('49', plain,
% 15.27/15.45      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 15.27/15.45       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 15.27/15.45       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 15.27/15.45      inference('simplify', [status(thm)], ['48'])).
% 15.27/15.45  thf('50', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf('51', plain,
% 15.27/15.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('split', [status(esa)], ['2'])).
% 15.27/15.45  thf('52', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('53', plain,
% 15.27/15.45      (((m1_subset_1 @ sk_D @ 
% 15.27/15.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['51', '52'])).
% 15.27/15.45  thf('54', plain,
% 15.27/15.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.27/15.45         ((v4_relat_1 @ X10 @ X11)
% 15.27/15.45          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 15.27/15.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.27/15.45  thf('55', plain,
% 15.27/15.45      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['53', '54'])).
% 15.27/15.45  thf('56', plain,
% 15.27/15.45      (![X6 : $i, X7 : $i]:
% 15.27/15.45         (~ (v4_relat_1 @ X6 @ X7)
% 15.27/15.45          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 15.27/15.45          | ~ (v1_relat_1 @ X6))),
% 15.27/15.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 15.27/15.45  thf('57', plain,
% 15.27/15.45      (((~ (v1_relat_1 @ sk_D)
% 15.27/15.45         | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['55', '56'])).
% 15.27/15.45  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('59', plain,
% 15.27/15.45      (((r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['57', '58'])).
% 15.27/15.45  thf('60', plain,
% 15.27/15.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['19', '20'])).
% 15.27/15.45  thf('61', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['59', '60'])).
% 15.27/15.45  thf('62', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | (r2_hidden @ (sk_C @ X24 @ X25) @ (k1_relat_1 @ X25))
% 15.27/15.45          | (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('63', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 15.27/15.45           | ~ (v1_relat_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | (r1_partfun1 @ X0 @ sk_D)
% 15.27/15.45           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 15.27/15.45           | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45           | ~ (v1_relat_1 @ sk_D)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['61', '62'])).
% 15.27/15.45  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('66', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 15.27/15.45           | ~ (v1_relat_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | (r1_partfun1 @ X0 @ sk_D)
% 15.27/15.45           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['63', '64', '65'])).
% 15.27/15.45  thf('67', plain,
% 15.27/15.45      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 15.27/15.45         | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['50', '66'])).
% 15.27/15.45  thf('68', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.27/15.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.27/15.45  thf('69', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('71', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('72', plain,
% 15.27/15.45      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ k1_xboole_0)
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 15.27/15.45  thf('73', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf('74', plain,
% 15.27/15.45      (![X27 : $i]:
% 15.27/15.45         (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45          | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))
% 15.27/15.45          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('75', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('76', plain,
% 15.27/15.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 15.27/15.45         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 15.27/15.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 15.27/15.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.27/15.45  thf('77', plain,
% 15.27/15.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 15.27/15.45      inference('sup-', [status(thm)], ['75', '76'])).
% 15.27/15.45  thf('78', plain,
% 15.27/15.45      (![X27 : $i]:
% 15.27/15.45         (~ (r2_hidden @ X27 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45          | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))
% 15.27/15.45          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('demod', [status(thm)], ['74', '77'])).
% 15.27/15.45  thf('79', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 15.27/15.45           | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['73', '78'])).
% 15.27/15.45  thf('80', plain,
% 15.27/15.45      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['72', '79'])).
% 15.27/15.45  thf('81', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('simplify', [status(thm)], ['80'])).
% 15.27/15.45  thf('82', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | ((k1_funct_1 @ X25 @ (sk_C @ X24 @ X25))
% 15.27/15.45              != (k1_funct_1 @ X24 @ (sk_C @ X24 @ X25)))
% 15.27/15.45          | (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('83', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_C_1)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['81', '82'])).
% 15.27/15.45  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('85', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('86', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 15.27/15.45         <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['18', '21'])).
% 15.27/15.45  thf('87', plain,
% 15.27/15.45      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['59', '60'])).
% 15.27/15.45  thf('88', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.27/15.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.27/15.45  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('91', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)],
% 15.27/15.45                ['83', '84', '85', '86', '87', '88', '89', '90'])).
% 15.27/15.45  thf('92', plain,
% 15.27/15.45      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 15.27/15.45      inference('simplify', [status(thm)], ['91'])).
% 15.27/15.45  thf('93', plain,
% 15.27/15.45      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 15.27/15.45      inference('split', [status(esa)], ['46'])).
% 15.27/15.45  thf('94', plain,
% 15.27/15.45      (~ (((sk_A) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('sup-', [status(thm)], ['92', '93'])).
% 15.27/15.45  thf('95', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('96', plain,
% 15.27/15.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.27/15.45         ((v4_relat_1 @ X10 @ X11)
% 15.27/15.45          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 15.27/15.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.27/15.45  thf('97', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 15.27/15.45      inference('sup-', [status(thm)], ['95', '96'])).
% 15.27/15.45  thf('98', plain,
% 15.27/15.45      (![X6 : $i, X7 : $i]:
% 15.27/15.45         (~ (v4_relat_1 @ X6 @ X7)
% 15.27/15.45          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 15.27/15.45          | ~ (v1_relat_1 @ X6))),
% 15.27/15.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 15.27/15.45  thf('99', plain,
% 15.27/15.45      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 15.27/15.45      inference('sup-', [status(thm)], ['97', '98'])).
% 15.27/15.45  thf('100', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('101', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 15.27/15.45      inference('demod', [status(thm)], ['99', '100'])).
% 15.27/15.45  thf(d1_funct_2, axiom,
% 15.27/15.45    (![A:$i,B:$i,C:$i]:
% 15.27/15.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.27/15.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.27/15.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.27/15.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.27/15.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.27/15.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.27/15.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.27/15.45  thf(zf_stmt_1, axiom,
% 15.27/15.45    (![B:$i,A:$i]:
% 15.27/15.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.27/15.45       ( zip_tseitin_0 @ B @ A ) ))).
% 15.27/15.45  thf('102', plain,
% 15.27/15.45      (![X16 : $i, X17 : $i]:
% 15.27/15.45         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.27/15.45  thf('103', plain,
% 15.27/15.45      (![X16 : $i, X17 : $i]:
% 15.27/15.45         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.27/15.45  thf('104', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 15.27/15.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.27/15.45  thf('105', plain,
% 15.27/15.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.27/15.45         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 15.27/15.45      inference('sup+', [status(thm)], ['103', '104'])).
% 15.27/15.45  thf('106', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.27/15.45  thf(zf_stmt_3, axiom,
% 15.27/15.45    (![C:$i,B:$i,A:$i]:
% 15.27/15.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.27/15.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.27/15.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.27/15.45  thf(zf_stmt_5, axiom,
% 15.27/15.45    (![A:$i,B:$i,C:$i]:
% 15.27/15.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.27/15.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.27/15.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.27/15.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.27/15.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.27/15.45  thf('107', plain,
% 15.27/15.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 15.27/15.45         (~ (zip_tseitin_0 @ X21 @ X22)
% 15.27/15.45          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 15.27/15.45          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.27/15.45  thf('108', plain,
% 15.27/15.45      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.27/15.45      inference('sup-', [status(thm)], ['106', '107'])).
% 15.27/15.45  thf('109', plain,
% 15.27/15.45      (![X0 : $i]:
% 15.27/15.45         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.27/15.45      inference('sup-', [status(thm)], ['105', '108'])).
% 15.27/15.45  thf('110', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('111', plain,
% 15.27/15.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.27/15.45         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 15.27/15.45          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 15.27/15.45          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.27/15.45  thf('112', plain,
% 15.27/15.45      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 15.27/15.45        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['110', '111'])).
% 15.27/15.45  thf('113', plain,
% 15.27/15.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('114', plain,
% 15.27/15.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 15.27/15.45         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 15.27/15.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 15.27/15.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.27/15.45  thf('115', plain,
% 15.27/15.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 15.27/15.45      inference('sup-', [status(thm)], ['113', '114'])).
% 15.27/15.45  thf('116', plain,
% 15.27/15.45      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.27/15.45      inference('demod', [status(thm)], ['112', '115'])).
% 15.27/15.45  thf('117', plain,
% 15.27/15.45      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['109', '116'])).
% 15.27/15.45  thf('118', plain,
% 15.27/15.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.27/15.45         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 15.27/15.45      inference('sup+', [status(thm)], ['103', '104'])).
% 15.27/15.45  thf('119', plain,
% 15.27/15.45      (![X0 : $i, X2 : $i]:
% 15.27/15.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.27/15.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.27/15.45  thf('120', plain,
% 15.27/15.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.27/15.45         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['118', '119'])).
% 15.27/15.45  thf('121', plain,
% 15.27/15.45      (![X0 : $i, X1 : $i]:
% 15.27/15.45         (((sk_A) = (k1_relat_1 @ sk_D))
% 15.27/15.45          | ((sk_B) = (X0))
% 15.27/15.45          | (zip_tseitin_0 @ X0 @ X1))),
% 15.27/15.45      inference('sup-', [status(thm)], ['117', '120'])).
% 15.27/15.45  thf('122', plain,
% 15.27/15.45      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('split', [status(esa)], ['2'])).
% 15.27/15.45  thf('123', plain,
% 15.27/15.45      ((![X0 : $i, X1 : $i]:
% 15.27/15.45          (((X0) != (k1_xboole_0))
% 15.27/15.45           | (zip_tseitin_0 @ X0 @ X1)
% 15.27/15.45           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['121', '122'])).
% 15.27/15.45  thf('124', plain,
% 15.27/15.45      ((![X1 : $i]:
% 15.27/15.45          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ k1_xboole_0 @ X1)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('simplify', [status(thm)], ['123'])).
% 15.27/15.45  thf('125', plain,
% 15.27/15.45      ((![X0 : $i, X1 : $i, X2 : $i]:
% 15.27/15.45          ((zip_tseitin_0 @ X0 @ X1)
% 15.27/15.45           | (zip_tseitin_0 @ X0 @ X2)
% 15.27/15.45           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['102', '124'])).
% 15.27/15.45  thf('126', plain,
% 15.27/15.45      ((![X0 : $i, X1 : $i]:
% 15.27/15.45          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('condensation', [status(thm)], ['125'])).
% 15.27/15.45  thf('127', plain,
% 15.27/15.45      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.27/15.45      inference('sup-', [status(thm)], ['106', '107'])).
% 15.27/15.45  thf('128', plain,
% 15.27/15.45      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['126', '127'])).
% 15.27/15.45  thf('129', plain,
% 15.27/15.45      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.27/15.45      inference('demod', [status(thm)], ['112', '115'])).
% 15.27/15.45  thf('130', plain,
% 15.27/15.45      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('clc', [status(thm)], ['128', '129'])).
% 15.27/15.45  thf('131', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | (r2_hidden @ (sk_C @ X24 @ X25) @ (k1_relat_1 @ X25))
% 15.27/15.45          | (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('132', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 15.27/15.45           | ~ (v1_relat_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | (r1_partfun1 @ X0 @ sk_D)
% 15.27/15.45           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 15.27/15.45           | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45           | ~ (v1_relat_1 @ sk_D)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['130', '131'])).
% 15.27/15.45  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('134', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('135', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 15.27/15.45           | ~ (v1_relat_1 @ X0)
% 15.27/15.45           | ~ (v1_funct_1 @ X0)
% 15.27/15.45           | (r1_partfun1 @ X0 @ sk_D)
% 15.27/15.45           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['132', '133', '134'])).
% 15.27/15.45  thf('136', plain,
% 15.27/15.45      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_C_1))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['101', '135'])).
% 15.27/15.45  thf('137', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('138', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('139', plain,
% 15.27/15.45      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['136', '137', '138'])).
% 15.27/15.45  thf('140', plain,
% 15.27/15.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 15.27/15.45      inference('sup-', [status(thm)], ['75', '76'])).
% 15.27/15.45  thf('141', plain,
% 15.27/15.45      ((![X27 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))))
% 15.27/15.45         <= ((![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('split', [status(esa)], ['0'])).
% 15.27/15.45  thf('142', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 15.27/15.45         <= ((![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['140', '141'])).
% 15.27/15.45  thf('143', plain,
% 15.27/15.45      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 15.27/15.45             (![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['139', '142'])).
% 15.27/15.45  thf('144', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | ((k1_funct_1 @ X25 @ (sk_C @ X24 @ X25))
% 15.27/15.45              != (k1_funct_1 @ X24 @ (sk_C @ X24 @ X25)))
% 15.27/15.45          | (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('145', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_C_1)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_D)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 15.27/15.45             (![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['143', '144'])).
% 15.27/15.45  thf('146', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('147', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('148', plain,
% 15.27/15.45      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('clc', [status(thm)], ['128', '129'])).
% 15.27/15.45  thf('149', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 15.27/15.45      inference('demod', [status(thm)], ['99', '100'])).
% 15.27/15.45  thf('150', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('151', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('152', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 15.27/15.45             (![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('demod', [status(thm)],
% 15.27/15.45                ['145', '146', '147', '148', '149', '150', '151'])).
% 15.27/15.45  thf('153', plain,
% 15.27/15.45      (((r1_partfun1 @ sk_C_1 @ sk_D))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 15.27/15.45             (![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('simplify', [status(thm)], ['152'])).
% 15.27/15.45  thf('154', plain,
% 15.27/15.45      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 15.27/15.45      inference('split', [status(esa)], ['46'])).
% 15.27/15.45  thf('155', plain,
% 15.27/15.45      ((((sk_B) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 15.27/15.45       ~
% 15.27/15.45       (![X27 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['153', '154'])).
% 15.27/15.45  thf('156', plain,
% 15.27/15.45      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 15.27/15.45       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('split', [status(esa)], ['46'])).
% 15.27/15.45  thf('157', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 15.27/15.45         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('split', [status(esa)], ['25'])).
% 15.27/15.45  thf('158', plain,
% 15.27/15.45      ((![X27 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))))
% 15.27/15.45         <= ((![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('split', [status(esa)], ['0'])).
% 15.27/15.45  thf('159', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 15.27/15.45             (![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['157', '158'])).
% 15.27/15.45  thf('160', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 15.27/15.45      inference('split', [status(esa)], ['46'])).
% 15.27/15.45  thf('161', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 15.27/15.45             (![X27 : $i]:
% 15.27/15.45                (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45                 | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['159', '160'])).
% 15.27/15.45  thf('162', plain,
% 15.27/15.45      (~
% 15.27/15.45       (![X27 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27)))) | 
% 15.27/15.45       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 15.27/15.45       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 15.27/15.45      inference('simplify', [status(thm)], ['161'])).
% 15.27/15.45  thf('163', plain,
% 15.27/15.45      (((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 15.27/15.45       (![X27 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))))),
% 15.27/15.45      inference('split', [status(esa)], ['0'])).
% 15.27/15.45  thf('164', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 15.27/15.45       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('split', [status(esa)], ['25'])).
% 15.27/15.45  thf('165', plain,
% 15.27/15.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 15.27/15.45      inference('sup-', [status(thm)], ['75', '76'])).
% 15.27/15.45  thf('166', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 15.27/15.45         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('split', [status(esa)], ['25'])).
% 15.27/15.45  thf('167', plain,
% 15.27/15.45      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1)))
% 15.27/15.45         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup+', [status(thm)], ['165', '166'])).
% 15.27/15.45  thf('168', plain,
% 15.27/15.45      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)], ['136', '137', '138'])).
% 15.27/15.45  thf('169', plain,
% 15.27/15.45      (![X27 : $i]:
% 15.27/15.45         (~ (r2_hidden @ X27 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45          | ((k1_funct_1 @ sk_C_1 @ X27) = (k1_funct_1 @ sk_D @ X27))
% 15.27/15.45          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 15.27/15.45      inference('demod', [status(thm)], ['74', '77'])).
% 15.27/15.45  thf('170', plain,
% 15.27/15.45      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['168', '169'])).
% 15.27/15.45  thf('171', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('simplify', [status(thm)], ['170'])).
% 15.27/15.45  thf('172', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | ((k1_funct_1 @ X25 @ (sk_C @ X24 @ X25))
% 15.27/15.45              != (k1_funct_1 @ X24 @ (sk_C @ X24 @ X25)))
% 15.27/15.45          | (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('173', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_C_1)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45         | ~ (v1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['171', '172'])).
% 15.27/15.45  thf('174', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('175', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('176', plain,
% 15.27/15.45      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('clc', [status(thm)], ['128', '129'])).
% 15.27/15.45  thf('177', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 15.27/15.45      inference('demod', [status(thm)], ['99', '100'])).
% 15.27/15.45  thf('178', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('179', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('180', plain,
% 15.27/15.45      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 15.27/15.45           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('demod', [status(thm)],
% 15.27/15.45                ['173', '174', '175', '176', '177', '178', '179'])).
% 15.27/15.45  thf('181', plain,
% 15.27/15.45      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('simplify', [status(thm)], ['180'])).
% 15.27/15.45  thf('182', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 15.27/15.45      inference('demod', [status(thm)], ['99', '100'])).
% 15.27/15.45  thf('183', plain,
% 15.27/15.45      (![X16 : $i, X17 : $i]:
% 15.27/15.45         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.27/15.45  thf('184', plain,
% 15.27/15.45      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 15.27/15.45      inference('sup-', [status(thm)], ['106', '107'])).
% 15.27/15.45  thf('185', plain,
% 15.27/15.45      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 15.27/15.45      inference('sup-', [status(thm)], ['183', '184'])).
% 15.27/15.45  thf('186', plain,
% 15.27/15.45      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.27/15.45      inference('demod', [status(thm)], ['112', '115'])).
% 15.27/15.45  thf('187', plain,
% 15.27/15.45      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['185', '186'])).
% 15.27/15.45  thf('188', plain,
% 15.27/15.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 15.27/15.45         (~ (v1_relat_1 @ X24)
% 15.27/15.45          | ~ (v1_funct_1 @ X24)
% 15.27/15.45          | ~ (r1_partfun1 @ X25 @ X24)
% 15.27/15.45          | ((k1_funct_1 @ X25 @ X26) = (k1_funct_1 @ X24 @ X26))
% 15.27/15.45          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X25))
% 15.27/15.45          | ~ (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 15.27/15.45          | ~ (v1_funct_1 @ X25)
% 15.27/15.45          | ~ (v1_relat_1 @ X25))),
% 15.27/15.45      inference('cnf', [status(esa)], [t132_partfun1])).
% 15.27/15.45  thf('189', plain,
% 15.27/15.45      (![X0 : $i, X1 : $i]:
% 15.27/15.45         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 15.27/15.45          | ((sk_B) = (k1_xboole_0))
% 15.27/15.45          | ~ (v1_relat_1 @ X0)
% 15.27/15.45          | ~ (v1_funct_1 @ X0)
% 15.27/15.45          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.27/15.45          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 15.27/15.45          | ~ (r1_partfun1 @ X0 @ sk_D)
% 15.27/15.45          | ~ (v1_funct_1 @ sk_D)
% 15.27/15.45          | ~ (v1_relat_1 @ sk_D))),
% 15.27/15.45      inference('sup-', [status(thm)], ['187', '188'])).
% 15.27/15.45  thf('190', plain, ((v1_funct_1 @ sk_D)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('191', plain, ((v1_relat_1 @ sk_D)),
% 15.27/15.45      inference('demod', [status(thm)], ['42', '43'])).
% 15.27/15.45  thf('192', plain,
% 15.27/15.45      (![X0 : $i, X1 : $i]:
% 15.27/15.45         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 15.27/15.45          | ((sk_B) = (k1_xboole_0))
% 15.27/15.45          | ~ (v1_relat_1 @ X0)
% 15.27/15.45          | ~ (v1_funct_1 @ X0)
% 15.27/15.45          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.27/15.45          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 15.27/15.45          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 15.27/15.45      inference('demod', [status(thm)], ['189', '190', '191'])).
% 15.27/15.45  thf('193', plain,
% 15.27/15.45      (![X0 : $i]:
% 15.27/15.45         (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45          | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 15.27/15.45          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45          | ~ (v1_funct_1 @ sk_C_1)
% 15.27/15.45          | ~ (v1_relat_1 @ sk_C_1)
% 15.27/15.45          | ((sk_B) = (k1_xboole_0)))),
% 15.27/15.45      inference('sup-', [status(thm)], ['182', '192'])).
% 15.27/15.45  thf('194', plain, ((v1_funct_1 @ sk_C_1)),
% 15.27/15.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.27/15.45  thf('195', plain, ((v1_relat_1 @ sk_C_1)),
% 15.27/15.45      inference('demod', [status(thm)], ['15', '16'])).
% 15.27/15.45  thf('196', plain,
% 15.27/15.45      (![X0 : $i]:
% 15.27/15.45         (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 15.27/15.45          | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 15.27/15.45          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45          | ((sk_B) = (k1_xboole_0)))),
% 15.27/15.45      inference('demod', [status(thm)], ['193', '194', '195'])).
% 15.27/15.45  thf('197', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (((sk_B) = (k1_xboole_0))
% 15.27/15.45           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['181', '196'])).
% 15.27/15.45  thf('198', plain,
% 15.27/15.45      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('split', [status(esa)], ['2'])).
% 15.27/15.45  thf('199', plain,
% 15.27/15.45      ((![X0 : $i]:
% 15.27/15.45          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 15.27/15.45           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))))),
% 15.27/15.45      inference('simplify_reflect-', [status(thm)], ['197', '198'])).
% 15.27/15.45  thf('200', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['167', '199'])).
% 15.27/15.45  thf('201', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 15.27/15.45      inference('split', [status(esa)], ['46'])).
% 15.27/15.45  thf('202', plain,
% 15.27/15.45      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 15.27/15.45         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 15.27/15.45             ~ (((sk_B) = (k1_xboole_0))) & 
% 15.27/15.45             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 15.27/15.45      inference('sup-', [status(thm)], ['200', '201'])).
% 15.27/15.45  thf('203', plain,
% 15.27/15.45      ((((sk_B) = (k1_xboole_0))) | 
% 15.27/15.45       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 15.27/15.45       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 15.27/15.45      inference('simplify', [status(thm)], ['202'])).
% 15.27/15.45  thf('204', plain,
% 15.27/15.45      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 15.27/15.45      inference('split', [status(esa)], ['2'])).
% 15.27/15.45  thf('205', plain, ($false),
% 15.27/15.45      inference('sat_resolution*', [status(thm)],
% 15.27/15.45                ['49', '94', '155', '156', '162', '163', '164', '203', '204'])).
% 15.27/15.45  
% 15.27/15.45  % SZS output end Refutation
% 15.27/15.45  
% 15.27/15.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
