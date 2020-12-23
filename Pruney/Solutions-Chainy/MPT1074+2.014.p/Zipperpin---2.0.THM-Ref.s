%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iV1hZASq4Y

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:24 EST 2020

% Result     : Theorem 21.46s
% Output     : Refutation 21.46s
% Verified   : 
% Statistics : Number of formulae       :  123 (1232 expanded)
%              Number of leaves         :   47 ( 391 expanded)
%              Depth                    :   25
%              Number of atoms          :  959 (17564 expanded)
%              Number of equality atoms :   36 ( 379 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_2 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','27','30'])).

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

thf('32',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relat_1 @ X41 )
       != X40 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X41 @ X42 @ X40 ) @ X41 @ X42 @ X40 )
      | ( zip_tseitin_3 @ X41 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ~ ( v1_funct_1 @ X41 )
      | ( zip_tseitin_3 @ X41 @ X42 @ ( k1_relat_1 @ X41 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X41 @ X42 @ ( k1_relat_1 @ X41 ) ) @ X41 @ X42 @ ( k1_relat_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','27','30'])).

thf('36',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','27','30'])).

thf('37',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','41'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k3_funct_2 @ X30 @ X31 @ X29 @ X32 )
        = ( k1_funct_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('55',plain,(
    ! [X43: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X43 ) @ sk_A )
      | ~ ( m1_subset_1 @ X43 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_2 @ X33 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X34 @ X33 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','40'])).

thf('62',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( zip_tseitin_3 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('65',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('67',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('69',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['4','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iV1hZASq4Y
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 21.46/21.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.46/21.64  % Solved by: fo/fo7.sh
% 21.46/21.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.46/21.64  % done 5684 iterations in 21.157s
% 21.46/21.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.46/21.64  % SZS output start Refutation
% 21.46/21.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.46/21.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.46/21.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 21.46/21.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.46/21.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.46/21.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.46/21.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 21.46/21.64  thf(sk_C_type, type, sk_C: $i).
% 21.46/21.64  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 21.46/21.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 21.46/21.64  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 21.46/21.64  thf(sk_A_type, type, sk_A: $i).
% 21.46/21.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.46/21.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.46/21.64  thf(sk_B_type, type, sk_B: $i).
% 21.46/21.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.46/21.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.46/21.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.46/21.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.46/21.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 21.46/21.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 21.46/21.64  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 21.46/21.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.46/21.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.46/21.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 21.46/21.64  thf(t191_funct_2, conjecture,
% 21.46/21.64    (![A:$i,B:$i]:
% 21.46/21.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 21.46/21.64       ( ![C:$i]:
% 21.46/21.64         ( ( ~( v1_xboole_0 @ C ) ) =>
% 21.46/21.64           ( ![D:$i]:
% 21.46/21.64             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 21.46/21.64                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.46/21.64               ( ( ![E:$i]:
% 21.46/21.64                   ( ( m1_subset_1 @ E @ B ) =>
% 21.46/21.64                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 21.46/21.64                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 21.46/21.64  thf(zf_stmt_0, negated_conjecture,
% 21.46/21.64    (~( ![A:$i,B:$i]:
% 21.46/21.64        ( ( ~( v1_xboole_0 @ B ) ) =>
% 21.46/21.64          ( ![C:$i]:
% 21.46/21.64            ( ( ~( v1_xboole_0 @ C ) ) =>
% 21.46/21.64              ( ![D:$i]:
% 21.46/21.64                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 21.46/21.64                    ( m1_subset_1 @
% 21.46/21.64                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.46/21.64                  ( ( ![E:$i]:
% 21.46/21.64                      ( ( m1_subset_1 @ E @ B ) =>
% 21.46/21.64                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 21.46/21.64                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 21.46/21.64    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 21.46/21.64  thf('0', plain,
% 21.46/21.64      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf('1', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(redefinition_k2_relset_1, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.46/21.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 21.46/21.64  thf('2', plain,
% 21.46/21.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.46/21.64         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 21.46/21.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 21.46/21.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.46/21.64  thf('3', plain,
% 21.46/21.64      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('sup-', [status(thm)], ['1', '2'])).
% 21.46/21.64  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 21.46/21.64      inference('demod', [status(thm)], ['0', '3'])).
% 21.46/21.64  thf(t5_funct_2, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 21.46/21.64       ( ( ( ![D:$i]:
% 21.46/21.64             ( ( r2_hidden @ D @ A ) =>
% 21.46/21.64               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 21.46/21.64           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 21.46/21.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.46/21.64           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 21.46/21.64  thf(zf_stmt_1, axiom,
% 21.46/21.64    (![D:$i,C:$i,B:$i,A:$i]:
% 21.46/21.64     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 21.46/21.64       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 21.46/21.64  thf('5', plain,
% 21.46/21.64      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 21.46/21.64         ((zip_tseitin_2 @ X33 @ X34 @ X35 @ X36) | (r2_hidden @ X33 @ X36))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.46/21.64  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(d1_funct_2, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.46/21.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.46/21.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.46/21.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.46/21.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.46/21.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.46/21.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.46/21.64  thf(zf_stmt_2, axiom,
% 21.46/21.64    (![C:$i,B:$i,A:$i]:
% 21.46/21.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.46/21.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.46/21.64  thf('7', plain,
% 21.46/21.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 21.46/21.64         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 21.46/21.64          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 21.46/21.64          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 21.46/21.64  thf('8', plain,
% 21.46/21.64      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 21.46/21.64        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 21.46/21.64      inference('sup-', [status(thm)], ['6', '7'])).
% 21.46/21.64  thf('9', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.46/21.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 21.46/21.64  thf(zf_stmt_5, axiom,
% 21.46/21.64    (![B:$i,A:$i]:
% 21.46/21.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.46/21.64       ( zip_tseitin_0 @ B @ A ) ))).
% 21.46/21.64  thf(zf_stmt_6, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.46/21.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.46/21.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.46/21.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.46/21.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.46/21.64  thf('10', plain,
% 21.46/21.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 21.46/21.64         (~ (zip_tseitin_0 @ X26 @ X27)
% 21.46/21.64          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 21.46/21.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_6])).
% 21.46/21.64  thf('11', plain,
% 21.46/21.64      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 21.46/21.64        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 21.46/21.64      inference('sup-', [status(thm)], ['9', '10'])).
% 21.46/21.64  thf('12', plain,
% 21.46/21.64      (![X21 : $i, X22 : $i]:
% 21.46/21.64         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.46/21.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 21.46/21.64  thf('13', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 21.46/21.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.46/21.64  thf('14', plain,
% 21.46/21.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.46/21.64         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 21.46/21.64      inference('sup+', [status(thm)], ['12', '13'])).
% 21.46/21.64  thf('15', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(dt_k2_relset_1, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.46/21.64       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 21.46/21.64  thf('16', plain,
% 21.46/21.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 21.46/21.64         ((m1_subset_1 @ (k2_relset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 21.46/21.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 21.46/21.64      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 21.46/21.64  thf('17', plain,
% 21.46/21.64      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ 
% 21.46/21.64        (k1_zfmisc_1 @ sk_C))),
% 21.46/21.64      inference('sup-', [status(thm)], ['15', '16'])).
% 21.46/21.64  thf('18', plain,
% 21.46/21.64      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('sup-', [status(thm)], ['1', '2'])).
% 21.46/21.64  thf('19', plain,
% 21.46/21.64      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_C))),
% 21.46/21.64      inference('demod', [status(thm)], ['17', '18'])).
% 21.46/21.64  thf(t3_subset, axiom,
% 21.46/21.64    (![A:$i,B:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 21.46/21.64  thf('20', plain,
% 21.46/21.64      (![X6 : $i, X7 : $i]:
% 21.46/21.64         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 21.46/21.64      inference('cnf', [status(esa)], [t3_subset])).
% 21.46/21.64  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 21.46/21.64      inference('sup-', [status(thm)], ['19', '20'])).
% 21.46/21.64  thf(t1_xboole_1, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 21.46/21.64       ( r1_tarski @ A @ C ) ))).
% 21.46/21.64  thf('22', plain,
% 21.46/21.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.46/21.64         (~ (r1_tarski @ X0 @ X1)
% 21.46/21.64          | ~ (r1_tarski @ X1 @ X2)
% 21.46/21.64          | (r1_tarski @ X0 @ X2))),
% 21.46/21.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 21.46/21.64  thf('23', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 21.46/21.64      inference('sup-', [status(thm)], ['21', '22'])).
% 21.46/21.64  thf('24', plain,
% 21.46/21.64      (![X0 : $i, X1 : $i]:
% 21.46/21.64         ((zip_tseitin_0 @ sk_C @ X1)
% 21.46/21.64          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 21.46/21.64      inference('sup-', [status(thm)], ['14', '23'])).
% 21.46/21.64  thf('25', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 21.46/21.64      inference('demod', [status(thm)], ['0', '3'])).
% 21.46/21.64  thf('26', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 21.46/21.64      inference('sup-', [status(thm)], ['24', '25'])).
% 21.46/21.64  thf('27', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 21.46/21.64      inference('demod', [status(thm)], ['11', '26'])).
% 21.46/21.64  thf('28', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(redefinition_k1_relset_1, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.46/21.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 21.46/21.64  thf('29', plain,
% 21.46/21.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 21.46/21.64         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 21.46/21.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 21.46/21.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.46/21.64  thf('30', plain,
% 21.46/21.64      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('sup-', [status(thm)], ['28', '29'])).
% 21.46/21.64  thf('31', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('demod', [status(thm)], ['8', '27', '30'])).
% 21.46/21.64  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 21.46/21.64  thf(zf_stmt_8, axiom,
% 21.46/21.64    (![C:$i,B:$i,A:$i]:
% 21.46/21.64     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 21.46/21.64       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.46/21.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 21.46/21.64  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 21.46/21.64  thf(zf_stmt_10, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 21.46/21.64       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 21.46/21.64           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 21.46/21.64         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 21.46/21.64  thf('32', plain,
% 21.46/21.64      (![X40 : $i, X41 : $i, X42 : $i]:
% 21.46/21.64         (((k1_relat_1 @ X41) != (X40))
% 21.46/21.64          | ~ (zip_tseitin_2 @ (sk_D @ X41 @ X42 @ X40) @ X41 @ X42 @ X40)
% 21.46/21.64          | (zip_tseitin_3 @ X41 @ X42 @ X40)
% 21.46/21.64          | ~ (v1_funct_1 @ X41)
% 21.46/21.64          | ~ (v1_relat_1 @ X41))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_10])).
% 21.46/21.64  thf('33', plain,
% 21.46/21.64      (![X41 : $i, X42 : $i]:
% 21.46/21.64         (~ (v1_relat_1 @ X41)
% 21.46/21.64          | ~ (v1_funct_1 @ X41)
% 21.46/21.64          | (zip_tseitin_3 @ X41 @ X42 @ (k1_relat_1 @ X41))
% 21.46/21.64          | ~ (zip_tseitin_2 @ (sk_D @ X41 @ X42 @ (k1_relat_1 @ X41)) @ X41 @ 
% 21.46/21.64               X42 @ (k1_relat_1 @ X41)))),
% 21.46/21.64      inference('simplify', [status(thm)], ['32'])).
% 21.46/21.64  thf('34', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 21.46/21.64             (k1_relat_1 @ sk_D_1))
% 21.46/21.64          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 21.46/21.64          | ~ (v1_funct_1 @ sk_D_1)
% 21.46/21.64          | ~ (v1_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('sup-', [status(thm)], ['31', '33'])).
% 21.46/21.64  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('demod', [status(thm)], ['8', '27', '30'])).
% 21.46/21.64  thf('36', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('demod', [status(thm)], ['8', '27', '30'])).
% 21.46/21.64  thf('37', plain, ((v1_funct_1 @ sk_D_1)),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf('38', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(cc1_relset_1, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i]:
% 21.46/21.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.46/21.64       ( v1_relat_1 @ C ) ))).
% 21.46/21.64  thf('39', plain,
% 21.46/21.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 21.46/21.64         ((v1_relat_1 @ X9)
% 21.46/21.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 21.46/21.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.46/21.64  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 21.46/21.64      inference('sup-', [status(thm)], ['38', '39'])).
% 21.46/21.64  thf('41', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 21.46/21.64      inference('demod', [status(thm)], ['34', '35', '36', '37', '40'])).
% 21.46/21.64  thf('42', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 21.46/21.64          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 21.46/21.64      inference('sup-', [status(thm)], ['5', '41'])).
% 21.46/21.64  thf(t1_subset, axiom,
% 21.46/21.64    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 21.46/21.64  thf('43', plain,
% 21.46/21.64      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 21.46/21.64      inference('cnf', [status(esa)], [t1_subset])).
% 21.46/21.64  thf('44', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 21.46/21.64      inference('sup-', [status(thm)], ['42', '43'])).
% 21.46/21.64  thf('45', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf(redefinition_k3_funct_2, axiom,
% 21.46/21.64    (![A:$i,B:$i,C:$i,D:$i]:
% 21.46/21.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 21.46/21.64         ( v1_funct_2 @ C @ A @ B ) & 
% 21.46/21.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.46/21.64         ( m1_subset_1 @ D @ A ) ) =>
% 21.46/21.64       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 21.46/21.64  thf('46', plain,
% 21.46/21.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 21.46/21.64         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 21.46/21.64          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 21.46/21.64          | ~ (v1_funct_1 @ X29)
% 21.46/21.64          | (v1_xboole_0 @ X30)
% 21.46/21.64          | ~ (m1_subset_1 @ X32 @ X30)
% 21.46/21.64          | ((k3_funct_2 @ X30 @ X31 @ X29 @ X32) = (k1_funct_1 @ X29 @ X32)))),
% 21.46/21.64      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 21.46/21.64  thf('47', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 21.46/21.64            = (k1_funct_1 @ sk_D_1 @ X0))
% 21.46/21.64          | ~ (m1_subset_1 @ X0 @ sk_B)
% 21.46/21.64          | (v1_xboole_0 @ sk_B)
% 21.46/21.64          | ~ (v1_funct_1 @ sk_D_1)
% 21.46/21.64          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 21.46/21.64      inference('sup-', [status(thm)], ['45', '46'])).
% 21.46/21.64  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf('49', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf('50', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 21.46/21.64            = (k1_funct_1 @ sk_D_1 @ X0))
% 21.46/21.64          | ~ (m1_subset_1 @ X0 @ sk_B)
% 21.46/21.64          | (v1_xboole_0 @ sk_B))),
% 21.46/21.64      inference('demod', [status(thm)], ['47', '48', '49'])).
% 21.46/21.64  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf('52', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         (~ (m1_subset_1 @ X0 @ sk_B)
% 21.46/21.64          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 21.46/21.64              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 21.46/21.64      inference('clc', [status(thm)], ['50', '51'])).
% 21.46/21.64  thf('53', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 21.46/21.64              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 21.46/21.64      inference('sup-', [status(thm)], ['44', '52'])).
% 21.46/21.64  thf('54', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 21.46/21.64      inference('sup-', [status(thm)], ['42', '43'])).
% 21.46/21.64  thf('55', plain,
% 21.46/21.64      (![X43 : $i]:
% 21.46/21.64         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X43) @ sk_A)
% 21.46/21.64          | ~ (m1_subset_1 @ X43 @ sk_B))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.46/21.64  thf('56', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (r2_hidden @ 
% 21.46/21.64             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 21.46/21.64             sk_A))),
% 21.46/21.64      inference('sup-', [status(thm)], ['54', '55'])).
% 21.46/21.64  thf('57', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 21.46/21.64           sk_A)
% 21.46/21.64          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 21.46/21.64      inference('sup+', [status(thm)], ['53', '56'])).
% 21.46/21.64  thf('58', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 21.46/21.64             sk_A))),
% 21.46/21.64      inference('simplify', [status(thm)], ['57'])).
% 21.46/21.64  thf('59', plain,
% 21.46/21.64      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 21.46/21.64         ((zip_tseitin_2 @ X33 @ X34 @ X35 @ X36)
% 21.46/21.64          | ~ (r2_hidden @ (k1_funct_1 @ X34 @ X33) @ X35))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.46/21.64  thf('60', plain,
% 21.46/21.64      (![X0 : $i, X1 : $i]:
% 21.46/21.64         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 21.46/21.64      inference('sup-', [status(thm)], ['58', '59'])).
% 21.46/21.64  thf('61', plain,
% 21.46/21.64      (![X0 : $i]:
% 21.46/21.64         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 21.46/21.64          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 21.46/21.64      inference('demod', [status(thm)], ['34', '35', '36', '37', '40'])).
% 21.46/21.64  thf('62', plain,
% 21.46/21.64      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 21.46/21.64        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 21.46/21.64      inference('sup-', [status(thm)], ['60', '61'])).
% 21.46/21.64  thf('63', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 21.46/21.64      inference('simplify', [status(thm)], ['62'])).
% 21.46/21.64  thf('64', plain,
% 21.46/21.64      (![X37 : $i, X38 : $i, X39 : $i]:
% 21.46/21.64         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 21.46/21.64          | ~ (zip_tseitin_3 @ X37 @ X38 @ X39))),
% 21.46/21.64      inference('cnf', [status(esa)], [zf_stmt_8])).
% 21.46/21.64  thf('65', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.46/21.64      inference('sup-', [status(thm)], ['63', '64'])).
% 21.46/21.64  thf('66', plain,
% 21.46/21.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 21.46/21.64         ((m1_subset_1 @ (k2_relset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 21.46/21.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 21.46/21.64      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 21.46/21.64  thf('67', plain,
% 21.46/21.64      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 21.46/21.64        (k1_zfmisc_1 @ sk_A))),
% 21.46/21.64      inference('sup-', [status(thm)], ['65', '66'])).
% 21.46/21.64  thf('68', plain,
% 21.46/21.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.46/21.64      inference('sup-', [status(thm)], ['63', '64'])).
% 21.46/21.64  thf('69', plain,
% 21.46/21.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.46/21.64         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 21.46/21.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 21.46/21.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.46/21.64  thf('70', plain,
% 21.46/21.64      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 21.46/21.64      inference('sup-', [status(thm)], ['68', '69'])).
% 21.46/21.64  thf('71', plain,
% 21.46/21.64      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 21.46/21.64      inference('demod', [status(thm)], ['67', '70'])).
% 21.46/21.64  thf('72', plain,
% 21.46/21.64      (![X6 : $i, X7 : $i]:
% 21.46/21.64         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 21.46/21.64      inference('cnf', [status(esa)], [t3_subset])).
% 21.46/21.64  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 21.46/21.64      inference('sup-', [status(thm)], ['71', '72'])).
% 21.46/21.64  thf('74', plain, ($false), inference('demod', [status(thm)], ['4', '73'])).
% 21.46/21.64  
% 21.46/21.64  % SZS output end Refutation
% 21.46/21.64  
% 21.46/21.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
