%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1332+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eUSsiQSuWy

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:30 EST 2020

% Result     : Theorem 18.28s
% Output     : Refutation 18.28s
% Verified   : 
% Statistics : Number of formulae       :  417 (6001 expanded)
%              Number of leaves         :   43 (1824 expanded)
%              Depth                    :   25
%              Number of atoms          : 4925 (90754 expanded)
%              Number of equality atoms :  251 (5127 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t55_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( v3_pre_topc @ D @ B )
                       => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
       => ( ( v3_pre_topc @ D @ B )
         => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) )).

thf(zf_stmt_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( v5_pre_topc @ C @ A @ B )
                  <=> ! [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_2])).

thf('0',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X35 @ X38 @ X36 @ X39 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X0 @ X2 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X35 @ X38 @ X36 @ X39 )
      | ( v3_pre_topc @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X35 @ X38 @ X36 @ X39 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X5 @ X0 @ X4 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_0 @ X1 @ X3 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ X3 ) @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X0 @ X5 @ X1 @ X4 )
      | ~ ( l1_pre_topc @ X1 )
      | ( zip_tseitin_0 @ X0 @ X3 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X3 ) @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_0 @ X1 @ X3 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X0 @ X2 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_1 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D_1 ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D_1 ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D_1 ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('26',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('28',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D_1 ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X40: $i] :
      ( ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( v4_pre_topc @ X6 @ X3 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,
    ( ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) @ sk_B ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_struct_0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) ) @ sk_A ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) ) @ sk_A ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t52_tops_2,axiom,(
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

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ( ( k2_struct_0 @ X32 )
        = k1_xboole_0 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) @ X34 @ ( k2_struct_0 @ X32 ) )
        = ( k2_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_tops_2])).

thf('56',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('64',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','59','60','61','62','63'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('68',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['64','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('77',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('83',plain,
    ( ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('85',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('92',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['80','93'])).

thf('95',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('97',plain,
    ( ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('99',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['94','107'])).

thf('109',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['77','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('111',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('112',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('116',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('118',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('119',plain,
    ( ( k3_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) )
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['109','119'])).

thf('121',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('122',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k8_relset_1 @ X0 @ X3 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) )
      = ( k8_relset_1 @ X0 @ X3 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('127',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_subset_1 @ X0 @ ( k8_relset_1 @ X0 @ X3 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k8_relset_1 @ X0 @ X3 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k8_relset_1 @ X0 @ X3 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) )
      = ( k8_relset_1 @ X0 @ X3 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['125','128','129'])).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('132',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      = ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      = ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) )
      = ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['130','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','135'])).

thf('137',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('139',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('142',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['137','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('152',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('154',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','156'])).

thf('158',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['109','119'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['136','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) )
        = ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('162',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['160','166'])).

thf('168',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('169',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','156'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['136','157','158'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ sk_D_1 ) @ sk_A )
        | ( ( k2_struct_0 @ sk_B )
          = k1_xboole_0 ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','177'])).

thf('179',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('180',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('181',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('182',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('183',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('184',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X3 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('185',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('188',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('189',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('190',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189'])).

thf('191',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('192',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189'])).

thf('194',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('195',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('197',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('199',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( v4_pre_topc @ ( sk_D @ X4 @ X3 @ X5 ) @ X3 )
      | ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('200',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('203',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('204',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('205',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['200','201','202','203','204'])).

thf('206',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['197','205'])).

thf('207',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['192','206'])).

thf('208',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['182','208'])).

thf('210',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('211',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('213',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('214',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) @ X38 @ X35 ) @ X37 )
      | ~ ( v3_pre_topc @ X35 @ X36 )
      | ~ ( zip_tseitin_0 @ X35 @ X38 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X3 @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) @ X2 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X3 @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('218',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ sk_B )
        | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) @ sk_B )
        | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) @ sk_A ) )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['212','217'])).

thf('219',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('221',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) @ sk_B )
        | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) @ sk_A ) )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['211','221'])).

thf('223',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('226',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['223','226'])).

thf('228',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('229',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('231',plain,
    ( ( ( k3_subset_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) @ ( k3_subset_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('233',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('234',plain,
    ( ( ( k3_subset_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) @ sk_C )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('236',plain,
    ( ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) @ sk_C ) )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['231','234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('238',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      = ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('239',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['236','239'])).

thf('241',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ( k3_subset_1 @ k1_xboole_0 @ ( k3_subset_1 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['236','239'])).

thf('244',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('245',plain,
    ( ! [X0: $i] :
        ( ( k3_subset_1 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('247',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['242','245','246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('249',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('250',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('251',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('252',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['250','253'])).

thf('255',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('256',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('257',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('258',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['249','257'])).

thf('259',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('260',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('261',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k3_subset_1 @ k1_xboole_0 @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) @ sk_A )
        | ~ ( m1_subset_1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( v4_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['248','261'])).

thf('263',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('264',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) @ sk_A )
        | ( v4_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ( v4_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['247','264'])).

thf('266',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) @ sk_A ) )
   <= ( ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['222','265'])).

thf('267',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('268',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('269',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ( ( k2_struct_0 @ X33 )
       != k1_xboole_0 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) @ X34 @ ( k2_struct_0 @ X32 ) )
        = ( k2_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_tops_2])).

thf('270',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('272',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('273',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('275',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('276',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['270','271','272','273','274','275'])).

thf('277',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['267','276'])).

thf('278',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('279',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('282',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) )
          = ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['280','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf('284',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('285',plain,
    ( ! [X0: $i] :
        ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) )
        = ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('286',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['242','245','246'])).

thf('287',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['266','285','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('289',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 @ ( sk_D @ X4 @ X3 @ X5 ) ) @ X5 )
      | ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('290',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('293',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('294',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('295',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('296',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['290','291','292','293','294','295'])).

thf('297',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['287','296'])).

thf('298',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('299',plain,
    ( ~ ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k2_struct_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) ) @ sk_A ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['242','245','246'])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('303',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('304',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('305',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('306',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('307',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['304','307'])).

thf('309',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('310',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('311',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['303','311'])).

thf('313',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('314',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('315',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ ( k3_subset_1 @ k1_xboole_0 @ X0 ) @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) @ sk_A )
        | ~ ( m1_subset_1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( v3_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['302','315'])).

thf('317',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('318',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) @ sk_A )
        | ( v3_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['316','317'])).

thf('319',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ( v3_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['301','318'])).

thf('320',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ( v3_pre_topc @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D_1 ) ) ) @ sk_A ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['300','319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) )
        = ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('322',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['242','245','246'])).

thf('323',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ sk_D_1 ) @ sk_A ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['320','321','322'])).

thf('324',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('325',plain,
    ( ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ sk_D_1 ) @ sk_A )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('327',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X35 @ X38 @ X36 @ X39 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X36 ) @ X38 @ X35 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('328',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['326','327'])).

thf('329',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['325','328'])).

thf('330',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('331',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('333',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','181','299','331','332'])).

thf('334',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['180','333'])).

thf('335',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 )
        | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ sk_D_1 ) @ sk_A ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['178','334'])).

thf('336',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('337',plain,
    ( ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ sk_D_1 ) @ sk_A )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['335','336'])).

thf('338',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['326','327'])).

thf('339',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('341',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,
    ( ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('343',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['211','221'])).

thf('344',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['160','166'])).

thf('345',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('346',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('347',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('349',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('350',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['347','348','349'])).

thf('351',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('352',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('353',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('355',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['353','354'])).

thf('356',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) @ X1 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['350','355'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['344','356'])).

thf('358',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('359',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','156'])).

thf('360',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['136','157','158'])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['357','358','359','360'])).

thf('362',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['343','361'])).

thf('363',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['290','291','292','293','294','295'])).

thf('364',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ! [X40: $i] :
        ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['362','363'])).

thf('365',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('366',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['179'])).

thf('368',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k2_struct_0 @ sk_B )
       != k1_xboole_0 )
      & ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('369',plain,
    ( $false
   <= ( ( ( k2_struct_0 @ sk_B )
       != k1_xboole_0 )
      & ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['368'])).

thf('370',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','181','299','331','332'])).

thf('371',plain,
    ( ~ ! [X40: $i] :
          ( zip_tseitin_0 @ X40 @ sk_C @ sk_B @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['369','370'])).

thf('372',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','341','342','371'])).


%------------------------------------------------------------------------------
