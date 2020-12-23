%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dhklpFjW3e

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:23 EST 2020

% Result     : Theorem 48.21s
% Output     : Refutation 48.21s
% Verified   : 
% Statistics : Number of formulae       :  130 (1359 expanded)
%              Number of leaves         :   49 ( 428 expanded)
%              Depth                    :   27
%              Number of atoms          : 1013 (18698 expanded)
%              Number of equality atoms :   37 ( 397 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('22',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','35'])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ X44 )
       != X43 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ X43 ) @ X44 @ X45 @ X43 )
      | ( zip_tseitin_3 @ X44 @ X45 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('38',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ( zip_tseitin_3 @ X44 @ X45 @ ( k1_relat_1 @ X44 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','35'])).

thf('41',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','35'])).

thf('42',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','46'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('51',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k3_funct_2 @ X33 @ X34 @ X32 @ X35 )
        = ( k1_funct_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('60',plain,(
    ! [X46: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X46 ) @ sk_A )
      | ~ ( m1_subset_1 @ X46 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X37 @ X36 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','45'])).

thf('67',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( zip_tseitin_3 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('70',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('72',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['4','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dhklpFjW3e
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 48.21/48.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 48.21/48.47  % Solved by: fo/fo7.sh
% 48.21/48.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 48.21/48.47  % done 9367 iterations in 47.997s
% 48.21/48.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 48.21/48.47  % SZS output start Refutation
% 48.21/48.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 48.21/48.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 48.21/48.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 48.21/48.47  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 48.21/48.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 48.21/48.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 48.21/48.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 48.21/48.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 48.21/48.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 48.21/48.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 48.21/48.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 48.21/48.47  thf(sk_A_type, type, sk_A: $i).
% 48.21/48.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 48.21/48.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 48.21/48.47  thf(sk_B_type, type, sk_B: $i).
% 48.21/48.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 48.21/48.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 48.21/48.47  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 48.21/48.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 48.21/48.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 48.21/48.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 48.21/48.47  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 48.21/48.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 48.21/48.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 48.21/48.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 48.21/48.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 48.21/48.47  thf(t191_funct_2, conjecture,
% 48.21/48.47    (![A:$i,B:$i]:
% 48.21/48.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 48.21/48.47       ( ![C:$i]:
% 48.21/48.47         ( ( ~( v1_xboole_0 @ C ) ) =>
% 48.21/48.47           ( ![D:$i]:
% 48.21/48.47             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 48.21/48.47                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 48.21/48.47               ( ( ![E:$i]:
% 48.21/48.47                   ( ( m1_subset_1 @ E @ B ) =>
% 48.21/48.47                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 48.21/48.47                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 48.21/48.47  thf(zf_stmt_0, negated_conjecture,
% 48.21/48.47    (~( ![A:$i,B:$i]:
% 48.21/48.47        ( ( ~( v1_xboole_0 @ B ) ) =>
% 48.21/48.47          ( ![C:$i]:
% 48.21/48.47            ( ( ~( v1_xboole_0 @ C ) ) =>
% 48.21/48.47              ( ![D:$i]:
% 48.21/48.47                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 48.21/48.47                    ( m1_subset_1 @
% 48.21/48.47                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 48.21/48.47                  ( ( ![E:$i]:
% 48.21/48.47                      ( ( m1_subset_1 @ E @ B ) =>
% 48.21/48.47                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 48.21/48.47                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 48.21/48.47    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 48.21/48.47  thf('0', plain,
% 48.21/48.47      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) @ sk_A)),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf('1', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(redefinition_k2_relset_1, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 48.21/48.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 48.21/48.47  thf('2', plain,
% 48.21/48.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 48.21/48.47         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 48.21/48.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 48.21/48.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 48.21/48.47  thf('3', plain,
% 48.21/48.47      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['1', '2'])).
% 48.21/48.47  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 48.21/48.47      inference('demod', [status(thm)], ['0', '3'])).
% 48.21/48.47  thf(t5_funct_2, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 48.21/48.47       ( ( ( ![D:$i]:
% 48.21/48.47             ( ( r2_hidden @ D @ A ) =>
% 48.21/48.47               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 48.21/48.47           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 48.21/48.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 48.21/48.47           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 48.21/48.47  thf(zf_stmt_1, axiom,
% 48.21/48.47    (![D:$i,C:$i,B:$i,A:$i]:
% 48.21/48.47     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 48.21/48.47       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 48.21/48.47  thf('5', plain,
% 48.21/48.47      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 48.21/48.47         ((zip_tseitin_2 @ X36 @ X37 @ X38 @ X39) | (r2_hidden @ X36 @ X39))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 48.21/48.47  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1)),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(d1_funct_2, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 48.21/48.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 48.21/48.47           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 48.21/48.47             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 48.21/48.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 48.21/48.47           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 48.21/48.47             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 48.21/48.47  thf(zf_stmt_2, axiom,
% 48.21/48.47    (![C:$i,B:$i,A:$i]:
% 48.21/48.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 48.21/48.47       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 48.21/48.47  thf('7', plain,
% 48.21/48.47      (![X26 : $i, X27 : $i, X28 : $i]:
% 48.21/48.47         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 48.21/48.47          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 48.21/48.47          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 48.21/48.47  thf('8', plain,
% 48.21/48.47      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 48.21/48.47        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1)))),
% 48.21/48.47      inference('sup-', [status(thm)], ['6', '7'])).
% 48.21/48.47  thf('9', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(redefinition_k1_relset_1, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 48.21/48.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 48.21/48.47  thf('10', plain,
% 48.21/48.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 48.21/48.47         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 48.21/48.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 48.21/48.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 48.21/48.47  thf('11', plain,
% 48.21/48.47      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['9', '10'])).
% 48.21/48.47  thf('12', plain,
% 48.21/48.47      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 48.21/48.47        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 48.21/48.47      inference('demod', [status(thm)], ['8', '11'])).
% 48.21/48.47  thf('13', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 48.21/48.47  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 48.21/48.47  thf(zf_stmt_5, axiom,
% 48.21/48.47    (![B:$i,A:$i]:
% 48.21/48.47     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 48.21/48.47       ( zip_tseitin_0 @ B @ A ) ))).
% 48.21/48.47  thf(zf_stmt_6, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 48.21/48.47       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 48.21/48.47         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 48.21/48.47           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 48.21/48.47             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 48.21/48.47  thf('14', plain,
% 48.21/48.47      (![X29 : $i, X30 : $i, X31 : $i]:
% 48.21/48.47         (~ (zip_tseitin_0 @ X29 @ X30)
% 48.21/48.47          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 48.21/48.47          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_6])).
% 48.21/48.47  thf('15', plain,
% 48.21/48.47      (((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 48.21/48.47        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 48.21/48.47      inference('sup-', [status(thm)], ['13', '14'])).
% 48.21/48.47  thf('16', plain,
% 48.21/48.47      (![X24 : $i, X25 : $i]:
% 48.21/48.47         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 48.21/48.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 48.21/48.47  thf('17', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 48.21/48.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 48.21/48.47  thf('18', plain,
% 48.21/48.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.21/48.47         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 48.21/48.47      inference('sup+', [status(thm)], ['16', '17'])).
% 48.21/48.47  thf(d3_tarski, axiom,
% 48.21/48.47    (![A:$i,B:$i]:
% 48.21/48.47     ( ( r1_tarski @ A @ B ) <=>
% 48.21/48.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 48.21/48.47  thf('19', plain,
% 48.21/48.47      (![X1 : $i, X3 : $i]:
% 48.21/48.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 48.21/48.47      inference('cnf', [status(esa)], [d3_tarski])).
% 48.21/48.47  thf('20', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(dt_k2_relset_1, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 48.21/48.47       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 48.21/48.47  thf('21', plain,
% 48.21/48.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 48.21/48.47         ((m1_subset_1 @ (k2_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 48.21/48.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 48.21/48.47      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 48.21/48.47  thf('22', plain,
% 48.21/48.47      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) @ 
% 48.21/48.47        (k1_zfmisc_1 @ sk_C_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['20', '21'])).
% 48.21/48.47  thf(t3_subset, axiom,
% 48.21/48.47    (![A:$i,B:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 48.21/48.47  thf('23', plain,
% 48.21/48.47      (![X7 : $i, X8 : $i]:
% 48.21/48.47         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 48.21/48.47      inference('cnf', [status(esa)], [t3_subset])).
% 48.21/48.47  thf('24', plain,
% 48.21/48.47      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) @ sk_C_1)),
% 48.21/48.47      inference('sup-', [status(thm)], ['22', '23'])).
% 48.21/48.47  thf('25', plain,
% 48.21/48.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.21/48.47         (~ (r2_hidden @ X0 @ X1)
% 48.21/48.47          | (r2_hidden @ X0 @ X2)
% 48.21/48.47          | ~ (r1_tarski @ X1 @ X2))),
% 48.21/48.47      inference('cnf', [status(esa)], [d3_tarski])).
% 48.21/48.47  thf('26', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((r2_hidden @ X0 @ sk_C_1)
% 48.21/48.47          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1)))),
% 48.21/48.47      inference('sup-', [status(thm)], ['24', '25'])).
% 48.21/48.47  thf('27', plain,
% 48.21/48.47      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['1', '2'])).
% 48.21/48.47  thf('28', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((r2_hidden @ X0 @ sk_C_1)
% 48.21/48.47          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 48.21/48.47      inference('demod', [status(thm)], ['26', '27'])).
% 48.21/48.47  thf('29', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 48.21/48.47          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D_1)) @ sk_C_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['19', '28'])).
% 48.21/48.47  thf(t7_ordinal1, axiom,
% 48.21/48.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 48.21/48.47  thf('30', plain,
% 48.21/48.47      (![X10 : $i, X11 : $i]:
% 48.21/48.47         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 48.21/48.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 48.21/48.47  thf('31', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 48.21/48.47          | ~ (r1_tarski @ sk_C_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_D_1))))),
% 48.21/48.47      inference('sup-', [status(thm)], ['29', '30'])).
% 48.21/48.47  thf('32', plain,
% 48.21/48.47      (![X0 : $i, X1 : $i]:
% 48.21/48.47         ((zip_tseitin_0 @ sk_C_1 @ X1)
% 48.21/48.47          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 48.21/48.47      inference('sup-', [status(thm)], ['18', '31'])).
% 48.21/48.47  thf('33', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 48.21/48.47      inference('demod', [status(thm)], ['0', '3'])).
% 48.21/48.47  thf('34', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 48.21/48.47      inference('sup-', [status(thm)], ['32', '33'])).
% 48.21/48.47  thf('35', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)),
% 48.21/48.47      inference('demod', [status(thm)], ['15', '34'])).
% 48.21/48.47  thf('36', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('demod', [status(thm)], ['12', '35'])).
% 48.21/48.47  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 48.21/48.47  thf(zf_stmt_8, axiom,
% 48.21/48.47    (![C:$i,B:$i,A:$i]:
% 48.21/48.47     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 48.21/48.47       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 48.21/48.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 48.21/48.47  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 48.21/48.47  thf(zf_stmt_10, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 48.21/48.47       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 48.21/48.47           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 48.21/48.47         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 48.21/48.47  thf('37', plain,
% 48.21/48.47      (![X43 : $i, X44 : $i, X45 : $i]:
% 48.21/48.47         (((k1_relat_1 @ X44) != (X43))
% 48.21/48.47          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ X43) @ X44 @ X45 @ X43)
% 48.21/48.47          | (zip_tseitin_3 @ X44 @ X45 @ X43)
% 48.21/48.47          | ~ (v1_funct_1 @ X44)
% 48.21/48.47          | ~ (v1_relat_1 @ X44))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_10])).
% 48.21/48.47  thf('38', plain,
% 48.21/48.47      (![X44 : $i, X45 : $i]:
% 48.21/48.47         (~ (v1_relat_1 @ X44)
% 48.21/48.47          | ~ (v1_funct_1 @ X44)
% 48.21/48.47          | (zip_tseitin_3 @ X44 @ X45 @ (k1_relat_1 @ X44))
% 48.21/48.47          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ (k1_relat_1 @ X44)) @ X44 @ 
% 48.21/48.47               X45 @ (k1_relat_1 @ X44)))),
% 48.21/48.47      inference('simplify', [status(thm)], ['37'])).
% 48.21/48.47  thf('39', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 48.21/48.47             (k1_relat_1 @ sk_D_1))
% 48.21/48.47          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 48.21/48.47          | ~ (v1_funct_1 @ sk_D_1)
% 48.21/48.47          | ~ (v1_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['36', '38'])).
% 48.21/48.47  thf('40', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('demod', [status(thm)], ['12', '35'])).
% 48.21/48.47  thf('41', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('demod', [status(thm)], ['12', '35'])).
% 48.21/48.47  thf('42', plain, ((v1_funct_1 @ sk_D_1)),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf('43', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(cc1_relset_1, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i]:
% 48.21/48.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 48.21/48.47       ( v1_relat_1 @ C ) ))).
% 48.21/48.47  thf('44', plain,
% 48.21/48.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 48.21/48.47         ((v1_relat_1 @ X12)
% 48.21/48.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 48.21/48.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 48.21/48.47  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 48.21/48.47      inference('sup-', [status(thm)], ['43', '44'])).
% 48.21/48.47  thf('46', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 48.21/48.47      inference('demod', [status(thm)], ['39', '40', '41', '42', '45'])).
% 48.21/48.47  thf('47', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 48.21/48.47          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 48.21/48.47      inference('sup-', [status(thm)], ['5', '46'])).
% 48.21/48.47  thf(t1_subset, axiom,
% 48.21/48.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 48.21/48.47  thf('48', plain,
% 48.21/48.47      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 48.21/48.47      inference('cnf', [status(esa)], [t1_subset])).
% 48.21/48.47  thf('49', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 48.21/48.47      inference('sup-', [status(thm)], ['47', '48'])).
% 48.21/48.47  thf('50', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf(redefinition_k3_funct_2, axiom,
% 48.21/48.47    (![A:$i,B:$i,C:$i,D:$i]:
% 48.21/48.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 48.21/48.47         ( v1_funct_2 @ C @ A @ B ) & 
% 48.21/48.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 48.21/48.47         ( m1_subset_1 @ D @ A ) ) =>
% 48.21/48.47       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 48.21/48.47  thf('51', plain,
% 48.21/48.47      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 48.21/48.47         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 48.21/48.47          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 48.21/48.47          | ~ (v1_funct_1 @ X32)
% 48.21/48.47          | (v1_xboole_0 @ X33)
% 48.21/48.47          | ~ (m1_subset_1 @ X35 @ X33)
% 48.21/48.47          | ((k3_funct_2 @ X33 @ X34 @ X32 @ X35) = (k1_funct_1 @ X32 @ X35)))),
% 48.21/48.47      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 48.21/48.47  thf('52', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0)
% 48.21/48.47            = (k1_funct_1 @ sk_D_1 @ X0))
% 48.21/48.47          | ~ (m1_subset_1 @ X0 @ sk_B)
% 48.21/48.47          | (v1_xboole_0 @ sk_B)
% 48.21/48.47          | ~ (v1_funct_1 @ sk_D_1)
% 48.21/48.47          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['50', '51'])).
% 48.21/48.47  thf('53', plain, ((v1_funct_1 @ sk_D_1)),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf('54', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1)),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf('55', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0)
% 48.21/48.47            = (k1_funct_1 @ sk_D_1 @ X0))
% 48.21/48.47          | ~ (m1_subset_1 @ X0 @ sk_B)
% 48.21/48.47          | (v1_xboole_0 @ sk_B))),
% 48.21/48.47      inference('demod', [status(thm)], ['52', '53', '54'])).
% 48.21/48.47  thf('56', plain, (~ (v1_xboole_0 @ sk_B)),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf('57', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         (~ (m1_subset_1 @ X0 @ sk_B)
% 48.21/48.47          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0)
% 48.21/48.47              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 48.21/48.47      inference('clc', [status(thm)], ['55', '56'])).
% 48.21/48.47  thf('58', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 48.21/48.47              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 48.21/48.47      inference('sup-', [status(thm)], ['49', '57'])).
% 48.21/48.47  thf('59', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 48.21/48.47      inference('sup-', [status(thm)], ['47', '48'])).
% 48.21/48.47  thf('60', plain,
% 48.21/48.47      (![X46 : $i]:
% 48.21/48.47         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X46) @ sk_A)
% 48.21/48.47          | ~ (m1_subset_1 @ X46 @ sk_B))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.21/48.47  thf('61', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (r2_hidden @ 
% 48.21/48.47             (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 48.21/48.47             sk_A))),
% 48.21/48.47      inference('sup-', [status(thm)], ['59', '60'])).
% 48.21/48.47  thf('62', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 48.21/48.47           sk_A)
% 48.21/48.47          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 48.21/48.47      inference('sup+', [status(thm)], ['58', '61'])).
% 48.21/48.47  thf('63', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 48.21/48.47             sk_A))),
% 48.21/48.47      inference('simplify', [status(thm)], ['62'])).
% 48.21/48.47  thf('64', plain,
% 48.21/48.47      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 48.21/48.47         ((zip_tseitin_2 @ X36 @ X37 @ X38 @ X39)
% 48.21/48.47          | ~ (r2_hidden @ (k1_funct_1 @ X37 @ X36) @ X38))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 48.21/48.47  thf('65', plain,
% 48.21/48.47      (![X0 : $i, X1 : $i]:
% 48.21/48.47         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['63', '64'])).
% 48.21/48.47  thf('66', plain,
% 48.21/48.47      (![X0 : $i]:
% 48.21/48.47         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 48.21/48.47          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 48.21/48.47      inference('demod', [status(thm)], ['39', '40', '41', '42', '45'])).
% 48.21/48.47  thf('67', plain,
% 48.21/48.47      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 48.21/48.47        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 48.21/48.47      inference('sup-', [status(thm)], ['65', '66'])).
% 48.21/48.47  thf('68', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 48.21/48.47      inference('simplify', [status(thm)], ['67'])).
% 48.21/48.47  thf('69', plain,
% 48.21/48.47      (![X40 : $i, X41 : $i, X42 : $i]:
% 48.21/48.47         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 48.21/48.47          | ~ (zip_tseitin_3 @ X40 @ X41 @ X42))),
% 48.21/48.47      inference('cnf', [status(esa)], [zf_stmt_8])).
% 48.21/48.47  thf('70', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 48.21/48.47      inference('sup-', [status(thm)], ['68', '69'])).
% 48.21/48.47  thf('71', plain,
% 48.21/48.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 48.21/48.47         ((m1_subset_1 @ (k2_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 48.21/48.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 48.21/48.47      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 48.21/48.47  thf('72', plain,
% 48.21/48.47      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 48.21/48.47        (k1_zfmisc_1 @ sk_A))),
% 48.21/48.47      inference('sup-', [status(thm)], ['70', '71'])).
% 48.21/48.47  thf('73', plain,
% 48.21/48.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 48.21/48.47      inference('sup-', [status(thm)], ['68', '69'])).
% 48.21/48.47  thf('74', plain,
% 48.21/48.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 48.21/48.47         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 48.21/48.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 48.21/48.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 48.21/48.47  thf('75', plain,
% 48.21/48.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 48.21/48.47      inference('sup-', [status(thm)], ['73', '74'])).
% 48.21/48.47  thf('76', plain,
% 48.21/48.47      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 48.21/48.47      inference('demod', [status(thm)], ['72', '75'])).
% 48.21/48.47  thf('77', plain,
% 48.21/48.47      (![X7 : $i, X8 : $i]:
% 48.21/48.47         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 48.21/48.47      inference('cnf', [status(esa)], [t3_subset])).
% 48.21/48.47  thf('78', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 48.21/48.47      inference('sup-', [status(thm)], ['76', '77'])).
% 48.21/48.47  thf('79', plain, ($false), inference('demod', [status(thm)], ['4', '78'])).
% 48.21/48.47  
% 48.21/48.47  % SZS output end Refutation
% 48.21/48.47  
% 48.21/48.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
