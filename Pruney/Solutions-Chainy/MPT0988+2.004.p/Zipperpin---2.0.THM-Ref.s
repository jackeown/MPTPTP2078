%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.APBg5bFT9s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:52 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  163 (2976 expanded)
%              Number of leaves         :   35 ( 904 expanded)
%              Depth                    :   27
%              Number of atoms          : 1451 (89062 expanded)
%              Number of equality atoms :  111 (9120 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t34_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( v2_funct_1 @ C )
              & ! [E: $i,F: $i] :
                  ( ( ( ( r2_hidden @ F @ A )
                      & ( ( k1_funct_1 @ C @ F )
                        = E ) )
                   => ( ( r2_hidden @ E @ B )
                      & ( ( k1_funct_1 @ D @ E )
                        = F ) ) )
                  & ( ( ( r2_hidden @ E @ B )
                      & ( ( k1_funct_1 @ D @ E )
                        = F ) )
                   => ( ( r2_hidden @ F @ A )
                      & ( ( k1_funct_1 @ C @ F )
                        = E ) ) ) ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( v2_funct_1 @ C )
                & ! [E: $i,F: $i] :
                    ( ( ( ( r2_hidden @ F @ A )
                        & ( ( k1_funct_1 @ C @ F )
                          = E ) )
                     => ( ( r2_hidden @ E @ B )
                        & ( ( k1_funct_1 @ D @ E )
                          = F ) ) )
                    & ( ( ( r2_hidden @ E @ B )
                        & ( ( k1_funct_1 @ D @ E )
                          = F ) )
                     => ( ( r2_hidden @ F @ A )
                        & ( ( k1_funct_1 @ C @ F )
                          = E ) ) ) ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_D ) @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('24',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_D ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','18','21','25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_D ) @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_D ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('37',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) @ sk_A )
    | ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['30','49'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X9 = X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ( ( k2_funct_1 @ sk_C_1 )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_D ) @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_D ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('64',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['30','49'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_D ) )
      | ( ( k2_funct_1 @ sk_C_1 )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','57','66','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_C_1 )
      = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','74','75'])).

thf('77',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r2_hidden @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ sk_A )
      | ( ( k1_funct_1 @ sk_D @ X28 )
       != X27 )
      | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X28 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('82',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ sk_D ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X28 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('96',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','93','96'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ( X7
        = ( k1_funct_1 @ ( k2_funct_1 @ X6 ) @ ( k1_funct_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['99','104','105','106'])).

thf('108',plain,
    ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','107'])).

thf('109',plain,(
    r2_hidden @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('110',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X27 )
        = X28 )
      | ( ( k1_funct_1 @ sk_D @ X28 )
       != X27 )
      | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ X28 ) )
        = X28 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('113',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ sk_D ) )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ X28 ) )
        = X28 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    = ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,
    ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['108','114'])).

thf('116',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X9 = X8 )
      | ( ( k1_funct_1 @ X9 @ ( sk_C @ X8 @ X9 ) )
       != ( k1_funct_1 @ X8 @ ( sk_C @ X8 @ X9 ) ) )
      | ( ( k1_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('117',plain,
    ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k1_relat_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_C_1 )
      = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('119',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['30','49'])).

thf('121',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('123',plain,
    ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_C_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122'])).

thf('124',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = sk_D ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.APBg5bFT9s
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:18:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.66/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.88  % Solved by: fo/fo7.sh
% 0.66/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.88  % done 247 iterations in 0.394s
% 0.66/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.88  % SZS output start Refutation
% 0.66/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.66/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.66/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.66/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.66/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.66/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.66/0.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.66/0.88  thf(t34_funct_2, conjecture,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.88       ( ![D:$i]:
% 0.66/0.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.88           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) & 
% 0.66/0.88               ( ![E:$i,F:$i]:
% 0.66/0.88                 ( ( ( ( r2_hidden @ F @ A ) & 
% 0.66/0.88                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.66/0.88                     ( ( r2_hidden @ E @ B ) & 
% 0.66/0.88                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.66/0.88                   ( ( ( r2_hidden @ E @ B ) & 
% 0.66/0.88                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.66/0.88                     ( ( r2_hidden @ F @ A ) & 
% 0.66/0.88                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.66/0.88             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.66/0.88               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.66/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.88        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.88            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.88          ( ![D:$i]:
% 0.66/0.88            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.88              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.66/0.88                  ( v2_funct_1 @ C ) & 
% 0.66/0.88                  ( ![E:$i,F:$i]:
% 0.66/0.88                    ( ( ( ( r2_hidden @ F @ A ) & 
% 0.66/0.88                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.66/0.88                        ( ( r2_hidden @ E @ B ) & 
% 0.66/0.88                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.66/0.88                      ( ( ( r2_hidden @ E @ B ) & 
% 0.66/0.88                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.66/0.88                        ( ( r2_hidden @ F @ A ) & 
% 0.66/0.88                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.66/0.88                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.66/0.88                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.66/0.88    inference('cnf.neg', [status(esa)], [t34_funct_2])).
% 0.66/0.88  thf('0', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(d1_funct_2, axiom,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.66/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.66/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.66/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.66/0.88  thf(zf_stmt_1, axiom,
% 0.66/0.88    (![C:$i,B:$i,A:$i]:
% 0.66/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.66/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.66/0.88  thf('2', plain,
% 0.66/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.66/0.88         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.66/0.88          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.66/0.88          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.88  thf('3', plain,
% 0.66/0.88      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.66/0.88        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.88  thf(zf_stmt_2, axiom,
% 0.66/0.88    (![B:$i,A:$i]:
% 0.66/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.66/0.88  thf('4', plain,
% 0.66/0.88      (![X16 : $i, X17 : $i]:
% 0.66/0.88         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.88  thf('5', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.66/0.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.66/0.88  thf(zf_stmt_5, axiom,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.66/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.66/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.66/0.88  thf('6', plain,
% 0.66/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.88         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.66/0.88          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.66/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.88  thf('7', plain,
% 0.66/0.88      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.88  thf('8', plain,
% 0.66/0.88      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['4', '7'])).
% 0.66/0.88  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.66/0.88      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.66/0.88  thf('11', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.88  thf('12', plain,
% 0.66/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.66/0.88         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.66/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.66/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.88  thf('13', plain,
% 0.66/0.88      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.88  thf('14', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.66/0.88  thf('15', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ 
% 0.66/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_D))))),
% 0.66/0.88      inference('demod', [status(thm)], ['0', '14'])).
% 0.66/0.88  thf(t31_funct_2, axiom,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.88       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.66/0.88         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.66/0.88           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.66/0.88           ( m1_subset_1 @
% 0.66/0.88             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.66/0.88  thf('16', plain,
% 0.66/0.88      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.88         (~ (v2_funct_1 @ X24)
% 0.66/0.88          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 0.66/0.88          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 0.66/0.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.66/0.88          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.66/0.88          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 0.66/0.88          | ~ (v1_funct_1 @ X24))),
% 0.66/0.88      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.66/0.88  thf('17', plain,
% 0.66/0.88      ((~ (v1_funct_1 @ sk_C_1)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_relat_1 @ sk_D))
% 0.66/0.88        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))
% 0.66/0.88        | ((k2_relset_1 @ sk_A @ (k1_relat_1 @ sk_D) @ sk_C_1)
% 0.66/0.88            != (k1_relat_1 @ sk_D))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.88  thf('18', plain, ((v1_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('19', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.66/0.88  thf('21', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['19', '20'])).
% 0.66/0.88  thf('22', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('23', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.66/0.88  thf('24', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.66/0.88  thf('25', plain,
% 0.66/0.88      (((k2_relset_1 @ sk_A @ (k1_relat_1 @ sk_D) @ sk_C_1)
% 0.66/0.88         = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.66/0.88  thf('26', plain, ((v2_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('27', plain,
% 0.66/0.88      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))
% 0.66/0.88        | ((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('demod', [status(thm)], ['17', '18', '21', '25', '26'])).
% 0.66/0.88  thf('28', plain,
% 0.66/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['27'])).
% 0.66/0.88  thf('29', plain,
% 0.66/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.66/0.88         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.66/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.66/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.88  thf('30', plain,
% 0.66/0.88      (((k1_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88         = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.66/0.88  thf('31', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ 
% 0.66/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_D))))),
% 0.66/0.88      inference('demod', [status(thm)], ['0', '14'])).
% 0.66/0.88  thf('32', plain,
% 0.66/0.88      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.88         (~ (v2_funct_1 @ X24)
% 0.66/0.88          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 0.66/0.88          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 0.66/0.88          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.66/0.88          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 0.66/0.88          | ~ (v1_funct_1 @ X24))),
% 0.66/0.88      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.66/0.88  thf('33', plain,
% 0.66/0.88      ((~ (v1_funct_1 @ sk_C_1)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_relat_1 @ sk_D))
% 0.66/0.88        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_D) @ sk_A)
% 0.66/0.88        | ((k2_relset_1 @ sk_A @ (k1_relat_1 @ sk_D) @ sk_C_1)
% 0.66/0.88            != (k1_relat_1 @ sk_D))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['31', '32'])).
% 0.66/0.88  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('35', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['19', '20'])).
% 0.66/0.88  thf('36', plain,
% 0.66/0.88      (((k2_relset_1 @ sk_A @ (k1_relat_1 @ sk_D) @ sk_C_1)
% 0.66/0.88         = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.66/0.88  thf('37', plain, ((v2_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('38', plain,
% 0.66/0.88      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_D) @ sk_A)
% 0.66/0.88        | ((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.66/0.88  thf('39', plain,
% 0.66/0.88      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.66/0.88      inference('simplify', [status(thm)], ['38'])).
% 0.66/0.88  thf('40', plain,
% 0.66/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.66/0.88         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.66/0.88          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.66/0.88          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.88  thf('41', plain,
% 0.66/0.88      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ (k1_relat_1 @ sk_D))
% 0.66/0.88        | ((k1_relat_1 @ sk_D)
% 0.66/0.88            = (k1_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ (k2_funct_1 @ sk_C_1))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.88  thf('42', plain,
% 0.66/0.88      (![X16 : $i, X17 : $i]:
% 0.66/0.88         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.88  thf('43', plain,
% 0.66/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['27'])).
% 0.66/0.88  thf('44', plain,
% 0.66/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.88         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.66/0.88          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.66/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.88  thf('45', plain,
% 0.66/0.88      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ (k1_relat_1 @ sk_D))
% 0.66/0.88        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['43', '44'])).
% 0.66/0.88  thf('46', plain,
% 0.66/0.88      ((((sk_A) = (k1_xboole_0))
% 0.66/0.88        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['42', '45'])).
% 0.66/0.88  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('48', plain,
% 0.66/0.88      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.66/0.88  thf('49', plain,
% 0.66/0.88      (((k1_relat_1 @ sk_D)
% 0.66/0.88         = (k1_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('demod', [status(thm)], ['41', '48'])).
% 0.66/0.88  thf('50', plain,
% 0.66/0.88      (((k1_relat_1 @ sk_D) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('sup+', [status(thm)], ['30', '49'])).
% 0.66/0.88  thf(t9_funct_1, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.88           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.66/0.88               ( ![C:$i]:
% 0.66/0.88                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.66/0.88                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.66/0.88             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.66/0.88  thf('51', plain,
% 0.66/0.88      (![X8 : $i, X9 : $i]:
% 0.66/0.88         (~ (v1_relat_1 @ X8)
% 0.66/0.88          | ~ (v1_funct_1 @ X8)
% 0.66/0.88          | ((X9) = (X8))
% 0.66/0.88          | (r2_hidden @ (sk_C @ X8 @ X9) @ (k1_relat_1 @ X9))
% 0.66/0.88          | ((k1_relat_1 @ X9) != (k1_relat_1 @ X8))
% 0.66/0.88          | ~ (v1_funct_1 @ X9)
% 0.66/0.88          | ~ (v1_relat_1 @ X9))),
% 0.66/0.88      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.66/0.88  thf('52', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (((k1_relat_1 @ sk_D) != (k1_relat_1 @ X0))
% 0.66/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88          | (r2_hidden @ (sk_C @ X0 @ (k2_funct_1 @ sk_C_1)) @ 
% 0.66/0.88             (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.66/0.88          | ((k2_funct_1 @ sk_C_1) = (X0))
% 0.66/0.88          | ~ (v1_funct_1 @ X0)
% 0.66/0.88          | ~ (v1_relat_1 @ X0))),
% 0.66/0.88      inference('sup-', [status(thm)], ['50', '51'])).
% 0.66/0.88  thf('53', plain,
% 0.66/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['27'])).
% 0.66/0.88  thf(cc2_relat_1, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( v1_relat_1 @ A ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.66/0.88  thf('54', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.66/0.88          | (v1_relat_1 @ X0)
% 0.66/0.88          | ~ (v1_relat_1 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.88  thf('55', plain,
% 0.66/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A))
% 0.66/0.88        | (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.66/0.88  thf(fc6_relat_1, axiom,
% 0.66/0.88    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.66/0.88  thf('56', plain,
% 0.66/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.66/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.88  thf('57', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('demod', [status(thm)], ['55', '56'])).
% 0.66/0.88  thf('58', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ 
% 0.66/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_D))))),
% 0.66/0.88      inference('demod', [status(thm)], ['0', '14'])).
% 0.66/0.88  thf('59', plain,
% 0.66/0.88      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.88         (~ (v2_funct_1 @ X24)
% 0.66/0.88          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 0.66/0.88          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 0.66/0.88          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.66/0.88          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 0.66/0.88          | ~ (v1_funct_1 @ X24))),
% 0.66/0.88      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.66/0.88  thf('60', plain,
% 0.66/0.88      ((~ (v1_funct_1 @ sk_C_1)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_relat_1 @ sk_D))
% 0.66/0.88        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88        | ((k2_relset_1 @ sk_A @ (k1_relat_1 @ sk_D) @ sk_C_1)
% 0.66/0.88            != (k1_relat_1 @ sk_D))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.66/0.88  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('62', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['19', '20'])).
% 0.66/0.88  thf('63', plain,
% 0.66/0.88      (((k2_relset_1 @ sk_A @ (k1_relat_1 @ sk_D) @ sk_C_1)
% 0.66/0.88         = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.66/0.88  thf('64', plain, ((v2_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('65', plain,
% 0.66/0.88      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88        | ((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.66/0.88  thf('66', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('simplify', [status(thm)], ['65'])).
% 0.66/0.88  thf('67', plain,
% 0.66/0.88      (((k1_relat_1 @ sk_D) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('sup+', [status(thm)], ['30', '49'])).
% 0.66/0.88  thf('68', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (((k1_relat_1 @ sk_D) != (k1_relat_1 @ X0))
% 0.66/0.88          | (r2_hidden @ (sk_C @ X0 @ (k2_funct_1 @ sk_C_1)) @ 
% 0.66/0.88             (k1_relat_1 @ sk_D))
% 0.66/0.88          | ((k2_funct_1 @ sk_C_1) = (X0))
% 0.66/0.88          | ~ (v1_funct_1 @ X0)
% 0.66/0.88          | ~ (v1_relat_1 @ X0))),
% 0.66/0.88      inference('demod', [status(thm)], ['52', '57', '66', '67'])).
% 0.66/0.88  thf('69', plain,
% 0.66/0.88      ((~ (v1_relat_1 @ sk_D)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.66/0.88        | ((k2_funct_1 @ sk_C_1) = (sk_D))
% 0.66/0.88        | (r2_hidden @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)) @ 
% 0.66/0.88           (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('eq_res', [status(thm)], ['68'])).
% 0.66/0.88  thf('70', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('71', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.66/0.88          | (v1_relat_1 @ X0)
% 0.66/0.88          | ~ (v1_relat_1 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.88  thf('72', plain,
% 0.66/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.66/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.66/0.88  thf('73', plain,
% 0.66/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.66/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.88  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.88      inference('demod', [status(thm)], ['72', '73'])).
% 0.66/0.88  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('76', plain,
% 0.66/0.88      ((((k2_funct_1 @ sk_C_1) = (sk_D))
% 0.66/0.88        | (r2_hidden @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)) @ 
% 0.66/0.88           (k1_relat_1 @ sk_D)))),
% 0.66/0.88      inference('demod', [status(thm)], ['69', '74', '75'])).
% 0.66/0.88  thf('77', plain, (((sk_D) != (k2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('78', plain,
% 0.66/0.88      ((r2_hidden @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)) @ (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.66/0.88  thf('79', plain,
% 0.66/0.88      (![X27 : $i, X28 : $i]:
% 0.66/0.88         ((r2_hidden @ X27 @ sk_A)
% 0.66/0.88          | ((k1_funct_1 @ sk_D @ X28) != (X27))
% 0.66/0.88          | ~ (r2_hidden @ X28 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('80', plain,
% 0.66/0.88      (![X28 : $i]:
% 0.66/0.88         (~ (r2_hidden @ X28 @ sk_B)
% 0.66/0.88          | (r2_hidden @ (k1_funct_1 @ sk_D @ X28) @ sk_A))),
% 0.66/0.88      inference('simplify', [status(thm)], ['79'])).
% 0.66/0.88  thf('81', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.66/0.88  thf('82', plain,
% 0.66/0.88      (![X28 : $i]:
% 0.66/0.88         (~ (r2_hidden @ X28 @ (k1_relat_1 @ sk_D))
% 0.66/0.88          | (r2_hidden @ (k1_funct_1 @ sk_D @ X28) @ sk_A))),
% 0.66/0.88      inference('demod', [status(thm)], ['80', '81'])).
% 0.66/0.88  thf('83', plain,
% 0.66/0.88      ((r2_hidden @ 
% 0.66/0.88        (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1))) @ sk_A)),
% 0.66/0.88      inference('sup-', [status(thm)], ['78', '82'])).
% 0.66/0.88  thf('84', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('85', plain,
% 0.66/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.66/0.88         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.66/0.88          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.66/0.88          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.88  thf('86', plain,
% 0.66/0.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.66/0.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['84', '85'])).
% 0.66/0.88  thf('87', plain,
% 0.66/0.88      (![X16 : $i, X17 : $i]:
% 0.66/0.88         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.88  thf('88', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('89', plain,
% 0.66/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.88         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.66/0.88          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.66/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.88  thf('90', plain,
% 0.66/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.66/0.88        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.66/0.88      inference('sup-', [status(thm)], ['88', '89'])).
% 0.66/0.88  thf('91', plain,
% 0.66/0.88      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.66/0.88      inference('sup-', [status(thm)], ['87', '90'])).
% 0.66/0.88  thf('92', plain, (((sk_B) != (k1_xboole_0))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('93', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.66/0.88      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.66/0.88  thf('94', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('95', plain,
% 0.66/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.66/0.88         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.66/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.66/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.88  thf('96', plain,
% 0.66/0.88      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['94', '95'])).
% 0.66/0.88  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.66/0.88      inference('demod', [status(thm)], ['86', '93', '96'])).
% 0.66/0.88  thf(t56_funct_1, axiom,
% 0.66/0.88    (![A:$i,B:$i]:
% 0.66/0.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.88       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.66/0.88         ( ( ( A ) =
% 0.66/0.88             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.66/0.88           ( ( A ) =
% 0.66/0.88             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.66/0.88  thf('98', plain,
% 0.66/0.88      (![X6 : $i, X7 : $i]:
% 0.66/0.88         (~ (v2_funct_1 @ X6)
% 0.66/0.88          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X6))
% 0.66/0.88          | ((X7) = (k1_funct_1 @ (k2_funct_1 @ X6) @ (k1_funct_1 @ X6 @ X7)))
% 0.66/0.88          | ~ (v1_funct_1 @ X6)
% 0.66/0.88          | ~ (v1_relat_1 @ X6))),
% 0.66/0.88      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.66/0.88  thf('99', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (~ (r2_hidden @ X0 @ sk_A)
% 0.66/0.88          | ~ (v1_relat_1 @ sk_C_1)
% 0.66/0.88          | ~ (v1_funct_1 @ sk_C_1)
% 0.66/0.88          | ((X0)
% 0.66/0.88              = (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88                 (k1_funct_1 @ sk_C_1 @ X0)))
% 0.66/0.88          | ~ (v2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['97', '98'])).
% 0.66/0.88  thf('100', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('101', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]:
% 0.66/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.66/0.88          | (v1_relat_1 @ X0)
% 0.66/0.88          | ~ (v1_relat_1 @ X1))),
% 0.66/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.88  thf('102', plain,
% 0.66/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.66/0.88      inference('sup-', [status(thm)], ['100', '101'])).
% 0.66/0.88  thf('103', plain,
% 0.66/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.66/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.88  thf('104', plain, ((v1_relat_1 @ sk_C_1)),
% 0.66/0.88      inference('demod', [status(thm)], ['102', '103'])).
% 0.66/0.88  thf('105', plain, ((v1_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('106', plain, ((v2_funct_1 @ sk_C_1)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('107', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (~ (r2_hidden @ X0 @ sk_A)
% 0.66/0.88          | ((X0)
% 0.66/0.88              = (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88                 (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.66/0.88      inference('demod', [status(thm)], ['99', '104', '105', '106'])).
% 0.66/0.88  thf('108', plain,
% 0.66/0.88      (((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)))
% 0.66/0.88         = (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88            (k1_funct_1 @ sk_C_1 @ 
% 0.66/0.88             (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['83', '107'])).
% 0.66/0.88  thf('109', plain,
% 0.66/0.88      ((r2_hidden @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)) @ (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.66/0.88  thf('110', plain,
% 0.66/0.88      (![X27 : $i, X28 : $i]:
% 0.66/0.88         (((k1_funct_1 @ sk_C_1 @ X27) = (X28))
% 0.66/0.88          | ((k1_funct_1 @ sk_D @ X28) != (X27))
% 0.66/0.88          | ~ (r2_hidden @ X28 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('111', plain,
% 0.66/0.88      (![X28 : $i]:
% 0.66/0.88         (~ (r2_hidden @ X28 @ sk_B)
% 0.66/0.88          | ((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D @ X28)) = (X28)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['110'])).
% 0.66/0.88  thf('112', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.66/0.88  thf('113', plain,
% 0.66/0.88      (![X28 : $i]:
% 0.66/0.88         (~ (r2_hidden @ X28 @ (k1_relat_1 @ sk_D))
% 0.66/0.88          | ((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D @ X28)) = (X28)))),
% 0.66/0.88      inference('demod', [status(thm)], ['111', '112'])).
% 0.66/0.88  thf('114', plain,
% 0.66/0.88      (((k1_funct_1 @ sk_C_1 @ 
% 0.66/0.88         (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1))))
% 0.66/0.88         = (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['109', '113'])).
% 0.66/0.88  thf('115', plain,
% 0.66/0.88      (((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)))
% 0.66/0.88         = (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.66/0.88            (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1))))),
% 0.66/0.88      inference('demod', [status(thm)], ['108', '114'])).
% 0.66/0.88  thf('116', plain,
% 0.66/0.88      (![X8 : $i, X9 : $i]:
% 0.66/0.88         (~ (v1_relat_1 @ X8)
% 0.66/0.88          | ~ (v1_funct_1 @ X8)
% 0.66/0.88          | ((X9) = (X8))
% 0.66/0.88          | ((k1_funct_1 @ X9 @ (sk_C @ X8 @ X9))
% 0.66/0.88              != (k1_funct_1 @ X8 @ (sk_C @ X8 @ X9)))
% 0.66/0.88          | ((k1_relat_1 @ X9) != (k1_relat_1 @ X8))
% 0.66/0.88          | ~ (v1_funct_1 @ X9)
% 0.66/0.88          | ~ (v1_relat_1 @ X9))),
% 0.66/0.88      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.66/0.88  thf('117', plain,
% 0.66/0.88      ((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)))
% 0.66/0.88          != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1))))
% 0.66/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.66/0.88        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k1_relat_1 @ sk_D))
% 0.66/0.88        | ((k2_funct_1 @ sk_C_1) = (sk_D))
% 0.66/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.66/0.88        | ~ (v1_relat_1 @ sk_D))),
% 0.66/0.88      inference('sup-', [status(thm)], ['115', '116'])).
% 0.66/0.88  thf('118', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('demod', [status(thm)], ['55', '56'])).
% 0.66/0.88  thf('119', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('simplify', [status(thm)], ['65'])).
% 0.66/0.88  thf('120', plain,
% 0.66/0.88      (((k1_relat_1 @ sk_D) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.66/0.88      inference('sup+', [status(thm)], ['30', '49'])).
% 0.66/0.88  thf('121', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.88      inference('demod', [status(thm)], ['72', '73'])).
% 0.66/0.88  thf('123', plain,
% 0.66/0.88      ((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1)))
% 0.66/0.88          != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ (k2_funct_1 @ sk_C_1))))
% 0.66/0.88        | ((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_D))
% 0.66/0.88        | ((k2_funct_1 @ sk_C_1) = (sk_D)))),
% 0.66/0.88      inference('demod', [status(thm)],
% 0.66/0.88                ['117', '118', '119', '120', '121', '122'])).
% 0.66/0.88  thf('124', plain, (((k2_funct_1 @ sk_C_1) = (sk_D))),
% 0.66/0.88      inference('simplify', [status(thm)], ['123'])).
% 0.66/0.88  thf('125', plain, (((sk_D) != (k2_funct_1 @ sk_C_1))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('126', plain, ($false),
% 0.66/0.88      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.66/0.88  
% 0.66/0.88  % SZS output end Refutation
% 0.66/0.88  
% 0.66/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
