%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMumqt3t0f

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:45 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  153 (1068 expanded)
%              Number of leaves         :   27 ( 302 expanded)
%              Depth                    :   28
%              Number of atoms          : 1315 (19334 expanded)
%              Number of equality atoms :  120 (1686 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('7',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('44',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('53',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
        = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
        = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('60',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('64',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','64','65'])).

thf('67',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','66'])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('70',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('82',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['67','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('85',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X3: $i] :
      ( zip_tseitin_0 @ X3 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','88'])).

thf('90',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['83','89'])).

thf('91',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('92',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','92'])).

thf('94',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['39','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['30','94'])).

thf('96',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('101',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['39','93'])).

thf('108',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    zip_tseitin_1 @ sk_C @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['105','110'])).

thf('112',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','111'])).

thf('113',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','111'])).

thf('114',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','112','113'])).

thf('115',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','114'])).

thf('116',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','92'])).

thf('117',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','117'])).

thf('119',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','118'])).

thf('120',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('124',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMumqt3t0f
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.69  % Solved by: fo/fo7.sh
% 0.42/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.69  % done 178 iterations in 0.232s
% 0.42/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.69  % SZS output start Refutation
% 0.42/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.69  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.69  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.69  thf(d3_struct_0, axiom,
% 0.42/0.69    (![A:$i]:
% 0.42/0.69     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.69  thf('0', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('1', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf(t52_tops_2, conjecture,
% 0.42/0.69    (![A:$i]:
% 0.42/0.69     ( ( l1_struct_0 @ A ) =>
% 0.42/0.69       ( ![B:$i]:
% 0.42/0.69         ( ( l1_struct_0 @ B ) =>
% 0.42/0.69           ( ![C:$i]:
% 0.42/0.69             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.69                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.69                 ( m1_subset_1 @
% 0.42/0.69                   C @ 
% 0.42/0.69                   ( k1_zfmisc_1 @
% 0.42/0.69                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.69               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.69                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.69                 ( ( k8_relset_1 @
% 0.42/0.69                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.42/0.69                     ( k2_struct_0 @ B ) ) =
% 0.42/0.69                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.42/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.69    (~( ![A:$i]:
% 0.42/0.69        ( ( l1_struct_0 @ A ) =>
% 0.42/0.69          ( ![B:$i]:
% 0.42/0.69            ( ( l1_struct_0 @ B ) =>
% 0.42/0.69              ( ![C:$i]:
% 0.42/0.69                ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.69                    ( v1_funct_2 @
% 0.42/0.69                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.69                    ( m1_subset_1 @
% 0.42/0.69                      C @ 
% 0.42/0.69                      ( k1_zfmisc_1 @
% 0.42/0.69                        ( k2_zfmisc_1 @
% 0.42/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.69                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.69                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.69                    ( ( k8_relset_1 @
% 0.42/0.69                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.42/0.69                        ( k2_struct_0 @ B ) ) =
% 0.42/0.69                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.42/0.69    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.42/0.69  thf('2', plain,
% 0.42/0.69      ((m1_subset_1 @ sk_C @ 
% 0.42/0.69        (k1_zfmisc_1 @ 
% 0.42/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('3', plain,
% 0.42/0.69      (((m1_subset_1 @ sk_C @ 
% 0.42/0.69         (k1_zfmisc_1 @ 
% 0.42/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.42/0.69  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('5', plain,
% 0.42/0.69      ((m1_subset_1 @ sk_C @ 
% 0.42/0.69        (k1_zfmisc_1 @ 
% 0.42/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.42/0.69  thf(t38_relset_1, axiom,
% 0.42/0.69    (![A:$i,B:$i,C:$i]:
% 0.42/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.69       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.42/0.69         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.69  thf('6', plain,
% 0.42/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.69         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.42/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.42/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.42/0.69  thf('7', plain,
% 0.42/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69         (u1_struct_0 @ sk_B))
% 0.42/0.69         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.42/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.69  thf('8', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('9', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('10', plain,
% 0.42/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.69  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('12', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.42/0.69  thf(d1_funct_2, axiom,
% 0.42/0.69    (![A:$i,B:$i,C:$i]:
% 0.42/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.69  thf(zf_stmt_1, axiom,
% 0.42/0.69    (![C:$i,B:$i,A:$i]:
% 0.42/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.69  thf('13', plain,
% 0.42/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.69         (~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.42/0.69          | ((X5) = (k1_relset_1 @ X5 @ X6 @ X7))
% 0.42/0.69          | ~ (zip_tseitin_1 @ X7 @ X6 @ X5))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.69  thf('14', plain,
% 0.42/0.69      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.42/0.69        | ((k2_struct_0 @ sk_A)
% 0.42/0.69            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.69  thf(zf_stmt_2, axiom,
% 0.42/0.69    (![B:$i,A:$i]:
% 0.42/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.69  thf('15', plain,
% 0.42/0.69      (![X3 : $i, X4 : $i]:
% 0.42/0.69         ((zip_tseitin_0 @ X3 @ X4) | ((X3) = (k1_xboole_0)))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.69  thf('16', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('17', plain,
% 0.42/0.69      ((m1_subset_1 @ sk_C @ 
% 0.42/0.69        (k1_zfmisc_1 @ 
% 0.42/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.69  thf(zf_stmt_5, axiom,
% 0.42/0.69    (![A:$i,B:$i,C:$i]:
% 0.42/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.69  thf('18', plain,
% 0.42/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.69         (~ (zip_tseitin_0 @ X8 @ X9)
% 0.42/0.69          | (zip_tseitin_1 @ X10 @ X8 @ X9)
% 0.42/0.69          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8))))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.69  thf('19', plain,
% 0.42/0.69      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.69        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.69  thf('20', plain,
% 0.42/0.69      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.42/0.69        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['16', '19'])).
% 0.42/0.69  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('22', plain,
% 0.42/0.69      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.69        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.69  thf('23', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('24', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('25', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('26', plain,
% 0.42/0.69      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.69      inference('sup+', [status(thm)], ['24', '25'])).
% 0.42/0.69  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('28', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.42/0.69      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.69  thf('29', plain,
% 0.42/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.69         (~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.42/0.69          | ((X5) = (k1_relset_1 @ X5 @ X6 @ X7))
% 0.42/0.69          | ~ (zip_tseitin_1 @ X7 @ X6 @ X5))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.69  thf('30', plain,
% 0.42/0.69      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.69        | ((u1_struct_0 @ sk_A)
% 0.42/0.69            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.69  thf('31', plain,
% 0.42/0.69      (![X3 : $i, X4 : $i]:
% 0.42/0.69         ((zip_tseitin_0 @ X3 @ X4) | ((X3) = (k1_xboole_0)))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.69  thf('32', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('33', plain,
% 0.42/0.69      ((m1_subset_1 @ sk_C @ 
% 0.42/0.69        (k1_zfmisc_1 @ 
% 0.42/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('34', plain,
% 0.42/0.69      (((m1_subset_1 @ sk_C @ 
% 0.42/0.69         (k1_zfmisc_1 @ 
% 0.42/0.69          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.69      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.69  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('36', plain,
% 0.42/0.69      ((m1_subset_1 @ sk_C @ 
% 0.42/0.69        (k1_zfmisc_1 @ 
% 0.42/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.42/0.69      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.69  thf('37', plain,
% 0.42/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.69         (~ (zip_tseitin_0 @ X8 @ X9)
% 0.42/0.69          | (zip_tseitin_1 @ X10 @ X8 @ X9)
% 0.42/0.69          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8))))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.69  thf('38', plain,
% 0.42/0.69      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.69        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.69  thf('39', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.42/0.69        | (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['31', '38'])).
% 0.42/0.69  thf('40', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.42/0.69        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('41', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.42/0.69         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.42/0.69      inference('split', [status(esa)], ['40'])).
% 0.42/0.69  thf('42', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('split', [status(esa)], ['40'])).
% 0.42/0.69  thf('43', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.42/0.69  thf('44', plain,
% 0.42/0.69      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.69  thf('45', plain,
% 0.42/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.69         (~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.42/0.69          | ((X5) = (k1_relset_1 @ X5 @ X6 @ X7))
% 0.42/0.69          | ~ (zip_tseitin_1 @ X7 @ X6 @ X5))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.69  thf('46', plain,
% 0.42/0.69      (((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ k1_xboole_0)
% 0.42/0.69         | ((k1_xboole_0)
% 0.42/0.69             = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.69  thf('47', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('48', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('49', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('split', [status(esa)], ['40'])).
% 0.42/0.69  thf('50', plain,
% 0.42/0.69      ((m1_subset_1 @ sk_C @ 
% 0.42/0.69        (k1_zfmisc_1 @ 
% 0.42/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.42/0.69  thf('51', plain,
% 0.42/0.69      (((m1_subset_1 @ sk_C @ 
% 0.42/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['49', '50'])).
% 0.42/0.69  thf('52', plain,
% 0.42/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.69         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.42/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.42/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.42/0.69  thf('53', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (u1_struct_0 @ sk_B))
% 0.42/0.69          = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.69  thf('54', plain,
% 0.42/0.69      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69           (u1_struct_0 @ sk_B))
% 0.42/0.69           = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.69         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['48', '53'])).
% 0.42/0.69  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('56', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (u1_struct_0 @ sk_B))
% 0.42/0.69          = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['54', '55'])).
% 0.42/0.69  thf('57', plain,
% 0.42/0.69      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69           (k2_struct_0 @ sk_B))
% 0.42/0.69           = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.69         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['47', '56'])).
% 0.42/0.69  thf('58', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('59', plain,
% 0.42/0.69      (((m1_subset_1 @ sk_C @ 
% 0.42/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['49', '50'])).
% 0.42/0.69  thf('60', plain,
% 0.42/0.69      ((((m1_subset_1 @ sk_C @ 
% 0.42/0.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.42/0.69         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['58', '59'])).
% 0.42/0.69  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('62', plain,
% 0.42/0.69      (((m1_subset_1 @ sk_C @ 
% 0.42/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['60', '61'])).
% 0.42/0.69  thf('63', plain,
% 0.42/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.69         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.42/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.42/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.42/0.69  thf('64', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B))
% 0.42/0.69          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.69  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('66', plain,
% 0.42/0.69      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.42/0.69          = (k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['57', '64', '65'])).
% 0.42/0.69  thf('67', plain,
% 0.42/0.69      (((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ k1_xboole_0)
% 0.42/0.69         | ((k1_xboole_0)
% 0.42/0.69             = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C))))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['46', '66'])).
% 0.42/0.69  thf('68', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('69', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('split', [status(esa)], ['40'])).
% 0.42/0.69  thf('70', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('71', plain,
% 0.42/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('72', plain,
% 0.42/0.69      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.69  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('74', plain,
% 0.42/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('demod', [status(thm)], ['72', '73'])).
% 0.42/0.69  thf('75', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['69', '74'])).
% 0.42/0.69  thf('76', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('split', [status(esa)], ['40'])).
% 0.42/0.69  thf('77', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['75', '76'])).
% 0.42/0.69  thf('78', plain,
% 0.42/0.69      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.42/0.69         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['68', '77'])).
% 0.42/0.69  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('80', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.69  thf('81', plain,
% 0.42/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B))
% 0.42/0.69          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.69  thf('82', plain,
% 0.42/0.69      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.42/0.69          != (k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['80', '81'])).
% 0.42/0.69  thf('83', plain,
% 0.42/0.69      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ k1_xboole_0))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('simplify_reflect-', [status(thm)], ['67', '82'])).
% 0.42/0.69  thf('84', plain,
% 0.42/0.69      (((m1_subset_1 @ sk_C @ 
% 0.42/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup+', [status(thm)], ['49', '50'])).
% 0.42/0.69  thf('85', plain,
% 0.42/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.69         (~ (zip_tseitin_0 @ X8 @ X9)
% 0.42/0.69          | (zip_tseitin_1 @ X10 @ X8 @ X9)
% 0.42/0.69          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8))))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.69  thf('86', plain,
% 0.42/0.69      ((((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ k1_xboole_0)
% 0.42/0.69         | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ k1_xboole_0)))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('sup-', [status(thm)], ['84', '85'])).
% 0.42/0.69  thf('87', plain,
% 0.42/0.69      (![X3 : $i, X4 : $i]:
% 0.42/0.69         ((zip_tseitin_0 @ X3 @ X4) | ((X4) != (k1_xboole_0)))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.69  thf('88', plain, (![X3 : $i]: (zip_tseitin_0 @ X3 @ k1_xboole_0)),
% 0.42/0.69      inference('simplify', [status(thm)], ['87'])).
% 0.42/0.69  thf('89', plain,
% 0.42/0.69      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ k1_xboole_0))
% 0.42/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.42/0.69      inference('demod', [status(thm)], ['86', '88'])).
% 0.42/0.69  thf('90', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.42/0.69      inference('demod', [status(thm)], ['83', '89'])).
% 0.42/0.69  thf('91', plain,
% 0.42/0.69      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.42/0.69       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.42/0.69      inference('split', [status(esa)], ['40'])).
% 0.42/0.69  thf('92', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.42/0.69      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.42/0.69  thf('93', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.42/0.69      inference('simpl_trail', [status(thm)], ['41', '92'])).
% 0.42/0.69  thf('94', plain,
% 0.42/0.69      ((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.42/0.69      inference('simplify_reflect-', [status(thm)], ['39', '93'])).
% 0.42/0.69  thf('95', plain,
% 0.42/0.69      (((u1_struct_0 @ sk_A)
% 0.42/0.69         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.42/0.69      inference('demod', [status(thm)], ['30', '94'])).
% 0.42/0.69  thf('96', plain,
% 0.42/0.69      ((((u1_struct_0 @ sk_A)
% 0.42/0.69          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup+', [status(thm)], ['23', '95'])).
% 0.42/0.69  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('98', plain,
% 0.42/0.69      (((u1_struct_0 @ sk_A)
% 0.42/0.69         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.42/0.69      inference('demod', [status(thm)], ['96', '97'])).
% 0.42/0.69  thf('99', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('100', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.42/0.69  thf('101', plain,
% 0.42/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.69      inference('sup+', [status(thm)], ['99', '100'])).
% 0.42/0.69  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('103', plain,
% 0.42/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.42/0.69      inference('demod', [status(thm)], ['101', '102'])).
% 0.42/0.69  thf('104', plain,
% 0.42/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.69         (~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.42/0.69          | ((X5) = (k1_relset_1 @ X5 @ X6 @ X7))
% 0.42/0.69          | ~ (zip_tseitin_1 @ X7 @ X6 @ X5))),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.69  thf('105', plain,
% 0.42/0.69      ((~ (zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.42/0.69        | ((k2_struct_0 @ sk_A)
% 0.42/0.69            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.42/0.69  thf('106', plain,
% 0.42/0.69      (![X11 : $i]:
% 0.42/0.69         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.42/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.69  thf('107', plain,
% 0.42/0.69      ((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.42/0.69      inference('simplify_reflect-', [status(thm)], ['39', '93'])).
% 0.42/0.69  thf('108', plain,
% 0.42/0.69      (((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup+', [status(thm)], ['106', '107'])).
% 0.42/0.69  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('110', plain,
% 0.42/0.69      ((zip_tseitin_1 @ sk_C @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('demod', [status(thm)], ['108', '109'])).
% 0.42/0.69  thf('111', plain,
% 0.42/0.69      (((k2_struct_0 @ sk_A)
% 0.42/0.69         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.42/0.69      inference('demod', [status(thm)], ['105', '110'])).
% 0.42/0.69  thf('112', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup+', [status(thm)], ['98', '111'])).
% 0.42/0.69  thf('113', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.42/0.69      inference('sup+', [status(thm)], ['98', '111'])).
% 0.42/0.69  thf('114', plain,
% 0.42/0.69      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.42/0.69        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.42/0.69      inference('demod', [status(thm)], ['22', '112', '113'])).
% 0.42/0.69  thf('115', plain,
% 0.42/0.69      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.42/0.69        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.42/0.69      inference('sup-', [status(thm)], ['15', '114'])).
% 0.42/0.69  thf('116', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.42/0.69      inference('simpl_trail', [status(thm)], ['41', '92'])).
% 0.42/0.69  thf('117', plain,
% 0.42/0.69      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('simplify_reflect-', [status(thm)], ['115', '116'])).
% 0.42/0.69  thf('118', plain,
% 0.42/0.69      (((k2_struct_0 @ sk_A)
% 0.42/0.69         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.42/0.69      inference('demod', [status(thm)], ['14', '117'])).
% 0.42/0.69  thf('119', plain,
% 0.42/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69         (u1_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('demod', [status(thm)], ['7', '118'])).
% 0.42/0.69  thf('120', plain,
% 0.42/0.69      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69          (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))
% 0.42/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.69      inference('sup+', [status(thm)], ['0', '119'])).
% 0.42/0.69  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.69  thf('122', plain,
% 0.42/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69         (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('demod', [status(thm)], ['120', '121'])).
% 0.42/0.69  thf('123', plain,
% 0.42/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.42/0.69      inference('demod', [status(thm)], ['72', '73'])).
% 0.42/0.69  thf('124', plain, ($false),
% 0.42/0.69      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 0.42/0.69  
% 0.42/0.69  % SZS output end Refutation
% 0.42/0.69  
% 0.42/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
