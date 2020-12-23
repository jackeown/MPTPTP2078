%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:32 EST 2020

% Result     : Theorem 10.35s
% Output     : CNFRefutation 10.68s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 672 expanded)
%              Number of leaves         :   36 ( 243 expanded)
%              Depth                    :    9
%              Number of atoms          :  398 (2342 expanded)
%              Number of equality atoms :   16 ( 138 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_15 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C)))
                       => ! [F,G] :
                            ( r2_hidden(k4_tarski(F,G),k4_relset_1(A,B,B,C,D,E))
                          <=> ? [H] :
                                ( m1_subset_1(H,B)
                                & r2_hidden(k4_tarski(F,H),D)
                                & r2_hidden(k4_tarski(H,G),E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    ! [C_338,A_339,B_340] :
      ( v1_relat_1(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_36,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_69,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_30,plain,(
    ! [A_110,B_111] :
      ( v1_relat_1(k5_relat_1(A_110,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7724,plain,(
    ! [C_1340,A_1342,F_1339,B_1341,D_1343,E_1338] :
      ( k4_relset_1(A_1342,B_1341,C_1340,D_1343,E_1338,F_1339) = k5_relat_1(E_1338,F_1339)
      | ~ m1_subset_1(F_1339,k1_zfmisc_1(k2_zfmisc_1(C_1340,D_1343)))
      | ~ m1_subset_1(E_1338,k1_zfmisc_1(k2_zfmisc_1(A_1342,B_1341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8177,plain,(
    ! [A_1415,B_1416,E_1417] :
      ( k4_relset_1(A_1415,B_1416,'#skF_8','#skF_9',E_1417,'#skF_11') = k5_relat_1(E_1417,'#skF_11')
      | ~ m1_subset_1(E_1417,k1_zfmisc_1(k2_zfmisc_1(A_1415,B_1416))) ) ),
    inference(resolution,[status(thm)],[c_36,c_7724])).

tff(c_8195,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_38,c_8177])).

tff(c_7850,plain,(
    ! [A_1367,B_1368,E_1369] :
      ( k4_relset_1(A_1367,B_1368,'#skF_8','#skF_9',E_1369,'#skF_11') = k5_relat_1(E_1369,'#skF_11')
      | ~ m1_subset_1(E_1369,k1_zfmisc_1(k2_zfmisc_1(A_1367,B_1368))) ) ),
    inference(resolution,[status(thm)],[c_36,c_7724])).

tff(c_7868,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_38,c_7850])).

tff(c_60,plain,
    ( m1_subset_1('#skF_14','#skF_8')
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_71,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_7825,plain,(
    ! [A_1363,D_1366,F_1365,E_1362,B_1364] :
      ( r2_hidden(k4_tarski(D_1366,E_1362),k5_relat_1(A_1363,B_1364))
      | ~ r2_hidden(k4_tarski(F_1365,E_1362),B_1364)
      | ~ r2_hidden(k4_tarski(D_1366,F_1365),A_1363)
      | ~ v1_relat_1(k5_relat_1(A_1363,B_1364))
      | ~ v1_relat_1(B_1364)
      | ~ v1_relat_1(A_1363) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7847,plain,(
    ! [D_1366,A_1363] :
      ( r2_hidden(k4_tarski(D_1366,'#skF_16'),k5_relat_1(A_1363,k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_1366,'#skF_15'),A_1363)
      | ~ v1_relat_1(k5_relat_1(A_1363,k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')))
      | ~ v1_relat_1(k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11'))
      | ~ v1_relat_1(A_1363) ) ),
    inference(resolution,[status(thm)],[c_71,c_7825])).

tff(c_7954,plain,(
    ! [D_1366,A_1363] :
      ( r2_hidden(k4_tarski(D_1366,'#skF_16'),k5_relat_1(A_1363,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_1366,'#skF_15'),A_1363)
      | ~ v1_relat_1(k5_relat_1(A_1363,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_1363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7868,c_7868,c_7868,c_7847])).

tff(c_7955,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_7954])).

tff(c_7958,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_7955])).

tff(c_7962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_7958])).

tff(c_7964,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_7954])).

tff(c_1592,plain,(
    ! [B_606,D_608,E_603,F_604,A_607,C_605] :
      ( k4_relset_1(A_607,B_606,C_605,D_608,E_603,F_604) = k5_relat_1(E_603,F_604)
      | ~ m1_subset_1(F_604,k1_zfmisc_1(k2_zfmisc_1(C_605,D_608)))
      | ~ m1_subset_1(E_603,k1_zfmisc_1(k2_zfmisc_1(A_607,B_606))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1599,plain,(
    ! [A_609,B_610,E_611] :
      ( k4_relset_1(A_609,B_610,'#skF_8','#skF_9',E_611,'#skF_11') = k5_relat_1(E_611,'#skF_11')
      | ~ m1_subset_1(E_611,k1_zfmisc_1(k2_zfmisc_1(A_609,B_610))) ) ),
    inference(resolution,[status(thm)],[c_36,c_1592])).

tff(c_1607,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_38,c_1599])).

tff(c_1614,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1607,c_71])).

tff(c_1648,plain,(
    ! [E_616,A_617,F_619,D_620,B_618] :
      ( r2_hidden(k4_tarski(D_620,E_616),k5_relat_1(A_617,B_618))
      | ~ r2_hidden(k4_tarski(F_619,E_616),B_618)
      | ~ r2_hidden(k4_tarski(D_620,F_619),A_617)
      | ~ v1_relat_1(k5_relat_1(A_617,B_618))
      | ~ v1_relat_1(B_618)
      | ~ v1_relat_1(A_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1653,plain,(
    ! [D_620,A_617] :
      ( r2_hidden(k4_tarski(D_620,'#skF_16'),k5_relat_1(A_617,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_620,'#skF_15'),A_617)
      | ~ v1_relat_1(k5_relat_1(A_617,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_617) ) ),
    inference(resolution,[status(thm)],[c_1614,c_1648])).

tff(c_1655,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_1653])).

tff(c_1658,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_1655])).

tff(c_1662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_1658])).

tff(c_1664,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_1727,plain,(
    ! [E_641,A_642,B_643,D_644] :
      ( r2_hidden(k4_tarski('#skF_1'(E_641,k5_relat_1(A_642,B_643),A_642,B_643,D_644),E_641),B_643)
      | ~ r2_hidden(k4_tarski(D_644,E_641),k5_relat_1(A_642,B_643))
      | ~ v1_relat_1(k5_relat_1(A_642,B_643))
      | ~ v1_relat_1(B_643)
      | ~ v1_relat_1(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1813,plain,(
    ! [B_660,D_658,E_661,A_659,A_662] :
      ( r2_hidden(k4_tarski('#skF_1'(E_661,k5_relat_1(A_662,B_660),A_662,B_660,D_658),E_661),A_659)
      | ~ m1_subset_1(B_660,k1_zfmisc_1(A_659))
      | ~ r2_hidden(k4_tarski(D_658,E_661),k5_relat_1(A_662,B_660))
      | ~ v1_relat_1(k5_relat_1(A_662,B_660))
      | ~ v1_relat_1(B_660)
      | ~ v1_relat_1(A_662) ) ),
    inference(resolution,[status(thm)],[c_1727,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2897,plain,(
    ! [D_819,E_822,B_817,A_818,C_820,D_821] :
      ( r2_hidden('#skF_1'(E_822,k5_relat_1(A_818,B_817),A_818,B_817,D_821),C_820)
      | ~ m1_subset_1(B_817,k1_zfmisc_1(k2_zfmisc_1(C_820,D_819)))
      | ~ r2_hidden(k4_tarski(D_821,E_822),k5_relat_1(A_818,B_817))
      | ~ v1_relat_1(k5_relat_1(A_818,B_817))
      | ~ v1_relat_1(B_817)
      | ~ v1_relat_1(A_818) ) ),
    inference(resolution,[status(thm)],[c_1813,c_6])).

tff(c_2911,plain,(
    ! [E_822,A_818,D_821] :
      ( r2_hidden('#skF_1'(E_822,k5_relat_1(A_818,'#skF_11'),A_818,'#skF_11',D_821),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_821,E_822),k5_relat_1(A_818,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_818,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_818) ) ),
    inference(resolution,[status(thm)],[c_36,c_2897])).

tff(c_2924,plain,(
    ! [E_823,A_824,D_825] :
      ( r2_hidden('#skF_1'(E_823,k5_relat_1(A_824,'#skF_11'),A_824,'#skF_11',D_825),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_825,E_823),k5_relat_1(A_824,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_824,'#skF_11'))
      | ~ v1_relat_1(A_824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2911])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2940,plain,(
    ! [E_829,A_830,D_831] :
      ( m1_subset_1('#skF_1'(E_829,k5_relat_1(A_830,'#skF_11'),A_830,'#skF_11',D_831),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_831,E_829),k5_relat_1(A_830,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_830,'#skF_11'))
      | ~ v1_relat_1(A_830) ) ),
    inference(resolution,[status(thm)],[c_2924,c_10])).

tff(c_2969,plain,
    ( m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1614,c_2940])).

tff(c_2981,plain,(
    m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1664,c_2969])).

tff(c_28,plain,(
    ! [D_102,E_103,A_11,B_63] :
      ( r2_hidden(k4_tarski(D_102,'#skF_1'(E_103,k5_relat_1(A_11,B_63),A_11,B_63,D_102)),A_11)
      | ~ r2_hidden(k4_tarski(D_102,E_103),k5_relat_1(A_11,B_63))
      | ~ v1_relat_1(k5_relat_1(A_11,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [H_335] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
      | ~ r2_hidden(k4_tarski(H_335,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_335),'#skF_10')
      | ~ m1_subset_1(H_335,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1590,plain,(
    ! [H_335] :
      ( ~ r2_hidden(k4_tarski(H_335,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_335),'#skF_10')
      | ~ m1_subset_1(H_335,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1738,plain,(
    ! [A_642,D_644] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'('#skF_16',k5_relat_1(A_642,'#skF_11'),A_642,'#skF_11',D_644)),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1(A_642,'#skF_11'),A_642,'#skF_11',D_644),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_644,'#skF_16'),k5_relat_1(A_642,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_642,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_642) ) ),
    inference(resolution,[status(thm)],[c_1727,c_1590])).

tff(c_5215,plain,(
    ! [A_1011,D_1012] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'('#skF_16',k5_relat_1(A_1011,'#skF_11'),A_1011,'#skF_11',D_1012)),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1(A_1011,'#skF_11'),A_1011,'#skF_11',D_1012),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1012,'#skF_16'),k5_relat_1(A_1011,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1011,'#skF_11'))
      | ~ v1_relat_1(A_1011) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1738])).

tff(c_5223,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_5215])).

tff(c_5230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_1664,c_1614,c_2981,c_5223])).

tff(c_5231,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5309,plain,(
    ! [B_1029,D_1031,C_1028,F_1027,E_1026,A_1030] :
      ( k4_relset_1(A_1030,B_1029,C_1028,D_1031,E_1026,F_1027) = k5_relat_1(E_1026,F_1027)
      | ~ m1_subset_1(F_1027,k1_zfmisc_1(k2_zfmisc_1(C_1028,D_1031)))
      | ~ m1_subset_1(E_1026,k1_zfmisc_1(k2_zfmisc_1(A_1030,B_1029))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5320,plain,(
    ! [A_1032,B_1033,E_1034] :
      ( k4_relset_1(A_1032,B_1033,'#skF_8','#skF_9',E_1034,'#skF_11') = k5_relat_1(E_1034,'#skF_11')
      | ~ m1_subset_1(E_1034,k1_zfmisc_1(k2_zfmisc_1(A_1032,B_1033))) ) ),
    inference(resolution,[status(thm)],[c_36,c_5309])).

tff(c_5333,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_38,c_5320])).

tff(c_5340,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5333,c_71])).

tff(c_5375,plain,(
    ! [D_1042,E_1038,F_1041,A_1039,B_1040] :
      ( r2_hidden(k4_tarski(D_1042,E_1038),k5_relat_1(A_1039,B_1040))
      | ~ r2_hidden(k4_tarski(F_1041,E_1038),B_1040)
      | ~ r2_hidden(k4_tarski(D_1042,F_1041),A_1039)
      | ~ v1_relat_1(k5_relat_1(A_1039,B_1040))
      | ~ v1_relat_1(B_1040)
      | ~ v1_relat_1(A_1039) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5384,plain,(
    ! [D_1042,A_1039] :
      ( r2_hidden(k4_tarski(D_1042,'#skF_16'),k5_relat_1(A_1039,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_1042,'#skF_15'),A_1039)
      | ~ v1_relat_1(k5_relat_1(A_1039,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_1039) ) ),
    inference(resolution,[status(thm)],[c_5340,c_5375])).

tff(c_5416,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_5384])).

tff(c_5419,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_5416])).

tff(c_5423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_5419])).

tff(c_5425,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_5384])).

tff(c_5484,plain,(
    ! [D_1078,E_1079,A_1080,B_1081] :
      ( r2_hidden(k4_tarski(D_1078,'#skF_1'(E_1079,k5_relat_1(A_1080,B_1081),A_1080,B_1081,D_1078)),A_1080)
      | ~ r2_hidden(k4_tarski(D_1078,E_1079),k5_relat_1(A_1080,B_1081))
      | ~ v1_relat_1(k5_relat_1(A_1080,B_1081))
      | ~ v1_relat_1(B_1081)
      | ~ v1_relat_1(A_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5426,plain,(
    ! [E_1057,A_1058,B_1059,D_1060] :
      ( r2_hidden(k4_tarski('#skF_1'(E_1057,k5_relat_1(A_1058,B_1059),A_1058,B_1059,D_1060),E_1057),B_1059)
      | ~ r2_hidden(k4_tarski(D_1060,E_1057),k5_relat_1(A_1058,B_1059))
      | ~ v1_relat_1(k5_relat_1(A_1058,B_1059))
      | ~ v1_relat_1(B_1059)
      | ~ v1_relat_1(A_1058) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [H_335] :
      ( r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11')
      | ~ r2_hidden(k4_tarski(H_335,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_335),'#skF_10')
      | ~ m1_subset_1(H_335,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5262,plain,(
    ! [H_335] :
      ( ~ r2_hidden(k4_tarski(H_335,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_335),'#skF_10')
      | ~ m1_subset_1(H_335,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_5431,plain,(
    ! [A_1058,D_1060] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'('#skF_16',k5_relat_1(A_1058,'#skF_11'),A_1058,'#skF_11',D_1060)),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1(A_1058,'#skF_11'),A_1058,'#skF_11',D_1060),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1060,'#skF_16'),k5_relat_1(A_1058,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1058,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1058) ) ),
    inference(resolution,[status(thm)],[c_5426,c_5262])).

tff(c_5448,plain,(
    ! [A_1058,D_1060] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'('#skF_16',k5_relat_1(A_1058,'#skF_11'),A_1058,'#skF_11',D_1060)),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1(A_1058,'#skF_11'),A_1058,'#skF_11',D_1060),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1060,'#skF_16'),k5_relat_1(A_1058,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1058,'#skF_11'))
      | ~ v1_relat_1(A_1058) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_5431])).

tff(c_5492,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5484,c_5448])).

tff(c_5511,plain,(
    ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_5425,c_5340,c_5492])).

tff(c_6530,plain,(
    ! [A_1231,A_1235,B_1232,E_1234,D_1233] :
      ( r2_hidden(k4_tarski('#skF_1'(E_1234,k5_relat_1(A_1231,B_1232),A_1231,B_1232,D_1233),E_1234),A_1235)
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(A_1235))
      | ~ r2_hidden(k4_tarski(D_1233,E_1234),k5_relat_1(A_1231,B_1232))
      | ~ v1_relat_1(k5_relat_1(A_1231,B_1232))
      | ~ v1_relat_1(B_1232)
      | ~ v1_relat_1(A_1231) ) ),
    inference(resolution,[status(thm)],[c_5426,c_8])).

tff(c_7441,plain,(
    ! [B_1317,A_1318,D_1319,C_1320,D_1322,E_1321] :
      ( r2_hidden('#skF_1'(E_1321,k5_relat_1(A_1318,B_1317),A_1318,B_1317,D_1322),C_1320)
      | ~ m1_subset_1(B_1317,k1_zfmisc_1(k2_zfmisc_1(C_1320,D_1319)))
      | ~ r2_hidden(k4_tarski(D_1322,E_1321),k5_relat_1(A_1318,B_1317))
      | ~ v1_relat_1(k5_relat_1(A_1318,B_1317))
      | ~ v1_relat_1(B_1317)
      | ~ v1_relat_1(A_1318) ) ),
    inference(resolution,[status(thm)],[c_6530,c_6])).

tff(c_7461,plain,(
    ! [E_1321,A_1318,D_1322] :
      ( r2_hidden('#skF_1'(E_1321,k5_relat_1(A_1318,'#skF_11'),A_1318,'#skF_11',D_1322),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1322,E_1321),k5_relat_1(A_1318,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1318,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1318) ) ),
    inference(resolution,[status(thm)],[c_36,c_7441])).

tff(c_7476,plain,(
    ! [E_1323,A_1324,D_1325] :
      ( r2_hidden('#skF_1'(E_1323,k5_relat_1(A_1324,'#skF_11'),A_1324,'#skF_11',D_1325),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1325,E_1323),k5_relat_1(A_1324,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1324,'#skF_11'))
      | ~ v1_relat_1(A_1324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_7461])).

tff(c_7614,plain,(
    ! [E_1332,A_1333,D_1334] :
      ( m1_subset_1('#skF_1'(E_1332,k5_relat_1(A_1333,'#skF_11'),A_1333,'#skF_11',D_1334),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1334,E_1332),k5_relat_1(A_1333,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1333,'#skF_11'))
      | ~ v1_relat_1(A_1333) ) ),
    inference(resolution,[status(thm)],[c_7476,c_10])).

tff(c_7658,plain,
    ( m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5340,c_7614])).

tff(c_7680,plain,(
    m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5425,c_7658])).

tff(c_7682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5511,c_7680])).

tff(c_7683,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_7829,plain,(
    ! [D_1366,A_1363] :
      ( r2_hidden(k4_tarski(D_1366,'#skF_13'),k5_relat_1(A_1363,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_1366,'#skF_14'),A_1363)
      | ~ v1_relat_1(k5_relat_1(A_1363,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1363) ) ),
    inference(resolution,[status(thm)],[c_7683,c_7825])).

tff(c_8008,plain,(
    ! [D_1384,A_1385] :
      ( r2_hidden(k4_tarski(D_1384,'#skF_13'),k5_relat_1(A_1385,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_1384,'#skF_14'),A_1385)
      | ~ v1_relat_1(k5_relat_1(A_1385,'#skF_11'))
      | ~ v1_relat_1(A_1385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_7829])).

tff(c_46,plain,(
    ! [H_335] :
      ( ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11'))
      | ~ r2_hidden(k4_tarski(H_335,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_335),'#skF_10')
      | ~ m1_subset_1(H_335,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7747,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_7873,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7868,c_7747])).

tff(c_8011,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_8008,c_7873])).

tff(c_8022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7964,c_5231,c_8011])).

tff(c_8024,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_8095,plain,(
    ! [D_1405,B_1403,E_1401,F_1404,A_1402] :
      ( r2_hidden(k4_tarski(D_1405,E_1401),k5_relat_1(A_1402,B_1403))
      | ~ r2_hidden(k4_tarski(F_1404,E_1401),B_1403)
      | ~ r2_hidden(k4_tarski(D_1405,F_1404),A_1402)
      | ~ v1_relat_1(k5_relat_1(A_1402,B_1403))
      | ~ v1_relat_1(B_1403)
      | ~ v1_relat_1(A_1402) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8110,plain,(
    ! [D_1405,A_1402] :
      ( r2_hidden(k4_tarski(D_1405,'#skF_13'),k5_relat_1(A_1402,k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_1405,'#skF_12'),A_1402)
      | ~ v1_relat_1(k5_relat_1(A_1402,k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')))
      | ~ v1_relat_1(k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11'))
      | ~ v1_relat_1(A_1402) ) ),
    inference(resolution,[status(thm)],[c_8024,c_8095])).

tff(c_8389,plain,(
    ! [D_1405,A_1402] :
      ( r2_hidden(k4_tarski(D_1405,'#skF_13'),k5_relat_1(A_1402,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_1405,'#skF_12'),A_1402)
      | ~ v1_relat_1(k5_relat_1(A_1402,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_1402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8195,c_8195,c_8195,c_8110])).

tff(c_8390,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_8389])).

tff(c_8393,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_8390])).

tff(c_8397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_8393])).

tff(c_8399,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_8389])).

tff(c_8205,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8195,c_71])).

tff(c_8232,plain,(
    ! [E_1418,A_1419,B_1420,D_1421] :
      ( r2_hidden(k4_tarski('#skF_1'(E_1418,k5_relat_1(A_1419,B_1420),A_1419,B_1420,D_1421),E_1418),B_1420)
      | ~ r2_hidden(k4_tarski(D_1421,E_1418),k5_relat_1(A_1419,B_1420))
      | ~ v1_relat_1(k5_relat_1(A_1419,B_1420))
      | ~ v1_relat_1(B_1420)
      | ~ v1_relat_1(A_1419) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8023,plain,(
    ! [H_335] :
      ( ~ r2_hidden(k4_tarski(H_335,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_335),'#skF_10')
      | ~ m1_subset_1(H_335,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_8237,plain,(
    ! [A_1419,D_1421] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'('#skF_16',k5_relat_1(A_1419,'#skF_11'),A_1419,'#skF_11',D_1421)),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1(A_1419,'#skF_11'),A_1419,'#skF_11',D_1421),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1421,'#skF_16'),k5_relat_1(A_1419,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1419,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1419) ) ),
    inference(resolution,[status(thm)],[c_8232,c_8023])).

tff(c_10942,plain,(
    ! [A_1722,D_1723] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'('#skF_16',k5_relat_1(A_1722,'#skF_11'),A_1722,'#skF_11',D_1723)),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1(A_1722,'#skF_11'),A_1722,'#skF_11',D_1723),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1723,'#skF_16'),k5_relat_1(A_1722,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1722,'#skF_11'))
      | ~ v1_relat_1(A_1722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_8237])).

tff(c_10950,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_10942])).

tff(c_10956,plain,(
    ~ m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_8399,c_8205,c_10950])).

tff(c_8714,plain,(
    ! [E_1526,A_1528,A_1530,D_1527,B_1529] :
      ( r2_hidden(k4_tarski('#skF_1'(E_1526,k5_relat_1(A_1528,B_1529),A_1528,B_1529,D_1527),E_1526),A_1530)
      | ~ m1_subset_1(B_1529,k1_zfmisc_1(A_1530))
      | ~ r2_hidden(k4_tarski(D_1527,E_1526),k5_relat_1(A_1528,B_1529))
      | ~ v1_relat_1(k5_relat_1(A_1528,B_1529))
      | ~ v1_relat_1(B_1529)
      | ~ v1_relat_1(A_1528) ) ),
    inference(resolution,[status(thm)],[c_8232,c_8])).

tff(c_12224,plain,(
    ! [A_1864,E_1859,B_1863,D_1861,D_1860,C_1862] :
      ( r2_hidden('#skF_1'(E_1859,k5_relat_1(A_1864,B_1863),A_1864,B_1863,D_1861),C_1862)
      | ~ m1_subset_1(B_1863,k1_zfmisc_1(k2_zfmisc_1(C_1862,D_1860)))
      | ~ r2_hidden(k4_tarski(D_1861,E_1859),k5_relat_1(A_1864,B_1863))
      | ~ v1_relat_1(k5_relat_1(A_1864,B_1863))
      | ~ v1_relat_1(B_1863)
      | ~ v1_relat_1(A_1864) ) ),
    inference(resolution,[status(thm)],[c_8714,c_6])).

tff(c_12259,plain,(
    ! [E_1859,A_1864,D_1861] :
      ( r2_hidden('#skF_1'(E_1859,k5_relat_1(A_1864,'#skF_11'),A_1864,'#skF_11',D_1861),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1861,E_1859),k5_relat_1(A_1864,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1864,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1864) ) ),
    inference(resolution,[status(thm)],[c_36,c_12224])).

tff(c_12279,plain,(
    ! [E_1865,A_1866,D_1867] :
      ( r2_hidden('#skF_1'(E_1865,k5_relat_1(A_1866,'#skF_11'),A_1866,'#skF_11',D_1867),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1867,E_1865),k5_relat_1(A_1866,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1866,'#skF_11'))
      | ~ v1_relat_1(A_1866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12259])).

tff(c_12450,plain,(
    ! [E_1875,A_1876,D_1877] :
      ( m1_subset_1('#skF_1'(E_1875,k5_relat_1(A_1876,'#skF_11'),A_1876,'#skF_11',D_1877),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1877,E_1875),k5_relat_1(A_1876,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1876,'#skF_11'))
      | ~ v1_relat_1(A_1876) ) ),
    inference(resolution,[status(thm)],[c_12279,c_10])).

tff(c_12534,plain,
    ( m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_8205,c_12450])).

tff(c_12580,plain,(
    m1_subset_1('#skF_1'('#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_10','#skF_11','#skF_15'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8399,c_12534])).

tff(c_12582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10956,c_12580])).

tff(c_12584,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12585,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_12590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12584,c_12585])).

tff(c_12591,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_12592,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11')
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12598,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_12657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12592,c_12598])).

tff(c_12658,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12870,plain,(
    ! [B_1965,F_1966,E_1963,D_1967,A_1964] :
      ( r2_hidden(k4_tarski(D_1967,E_1963),k5_relat_1(A_1964,B_1965))
      | ~ r2_hidden(k4_tarski(F_1966,E_1963),B_1965)
      | ~ r2_hidden(k4_tarski(D_1967,F_1966),A_1964)
      | ~ v1_relat_1(k5_relat_1(A_1964,B_1965))
      | ~ v1_relat_1(B_1965)
      | ~ v1_relat_1(A_1964) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12878,plain,(
    ! [D_1967,A_1964] :
      ( r2_hidden(k4_tarski(D_1967,'#skF_13'),k5_relat_1(A_1964,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_1967,'#skF_14'),A_1964)
      | ~ v1_relat_1(k5_relat_1(A_1964,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1964) ) ),
    inference(resolution,[status(thm)],[c_12658,c_12870])).

tff(c_12954,plain,(
    ! [D_1982,A_1983] :
      ( r2_hidden(k4_tarski(D_1982,'#skF_13'),k5_relat_1(A_1983,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_1982,'#skF_14'),A_1983)
      | ~ v1_relat_1(k5_relat_1(A_1983,'#skF_11'))
      | ~ v1_relat_1(A_1983) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12878])).

tff(c_12809,plain,(
    ! [F_1953,E_1952,D_1957,C_1954,A_1956,B_1955] :
      ( k4_relset_1(A_1956,B_1955,C_1954,D_1957,E_1952,F_1953) = k5_relat_1(E_1952,F_1953)
      | ~ m1_subset_1(F_1953,k1_zfmisc_1(k2_zfmisc_1(C_1954,D_1957)))
      | ~ m1_subset_1(E_1952,k1_zfmisc_1(k2_zfmisc_1(A_1956,B_1955))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12841,plain,(
    ! [A_1960,B_1961,E_1962] :
      ( k4_relset_1(A_1960,B_1961,'#skF_8','#skF_9',E_1962,'#skF_11') = k5_relat_1(E_1962,'#skF_11')
      | ~ m1_subset_1(E_1962,k1_zfmisc_1(k2_zfmisc_1(A_1960,B_1961))) ) ),
    inference(resolution,[status(thm)],[c_36,c_12809])).

tff(c_12859,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_38,c_12841])).

tff(c_12659,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11'))
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12791,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_12659,c_54])).

tff(c_12864,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12859,c_12791])).

tff(c_12957,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_12954,c_12864])).

tff(c_12967,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12591,c_12957])).

tff(c_12973,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_12967])).

tff(c_12977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_12973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.35/4.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/4.04  
% 10.35/4.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/4.04  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_15 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3 > #skF_12
% 10.35/4.04  
% 10.35/4.04  %Foreground sorts:
% 10.35/4.04  
% 10.35/4.04  
% 10.35/4.04  %Background operators:
% 10.35/4.04  
% 10.35/4.04  
% 10.35/4.04  %Foreground operators:
% 10.35/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.35/4.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.35/4.04  tff('#skF_11', type, '#skF_11': $i).
% 10.35/4.04  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.35/4.04  tff('#skF_15', type, '#skF_15': $i).
% 10.35/4.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.35/4.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.35/4.04  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.35/4.04  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.35/4.04  tff('#skF_7', type, '#skF_7': $i).
% 10.35/4.04  tff('#skF_10', type, '#skF_10': $i).
% 10.35/4.04  tff('#skF_16', type, '#skF_16': $i).
% 10.35/4.04  tff('#skF_14', type, '#skF_14': $i).
% 10.35/4.04  tff('#skF_13', type, '#skF_13': $i).
% 10.35/4.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.35/4.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.35/4.04  tff('#skF_9', type, '#skF_9': $i).
% 10.35/4.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.35/4.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 10.35/4.04  tff('#skF_8', type, '#skF_8': $i).
% 10.35/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.35/4.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.35/4.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.35/4.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.35/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.35/4.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.35/4.04  tff('#skF_12', type, '#skF_12': $i).
% 10.35/4.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.35/4.04  
% 10.68/4.09  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (![F, G]: (r2_hidden(k4_tarski(F, G), k4_relset_1(A, B, B, C, D, E)) <=> (?[H]: ((m1_subset_1(H, B) & r2_hidden(k4_tarski(F, H), D)) & r2_hidden(k4_tarski(H, G), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_relset_1)).
% 10.68/4.09  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.68/4.09  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 10.68/4.09  tff(f_76, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 10.68/4.09  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 10.68/4.09  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.68/4.09  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.68/4.09  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 10.68/4.09  tff(c_38, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_62, plain, (![C_338, A_339, B_340]: (v1_relat_1(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.68/4.09  tff(c_70, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_38, c_62])).
% 10.68/4.09  tff(c_36, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_69, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_62])).
% 10.68/4.09  tff(c_30, plain, (![A_110, B_111]: (v1_relat_1(k5_relat_1(A_110, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.68/4.09  tff(c_7724, plain, (![C_1340, A_1342, F_1339, B_1341, D_1343, E_1338]: (k4_relset_1(A_1342, B_1341, C_1340, D_1343, E_1338, F_1339)=k5_relat_1(E_1338, F_1339) | ~m1_subset_1(F_1339, k1_zfmisc_1(k2_zfmisc_1(C_1340, D_1343))) | ~m1_subset_1(E_1338, k1_zfmisc_1(k2_zfmisc_1(A_1342, B_1341))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.68/4.09  tff(c_8177, plain, (![A_1415, B_1416, E_1417]: (k4_relset_1(A_1415, B_1416, '#skF_8', '#skF_9', E_1417, '#skF_11')=k5_relat_1(E_1417, '#skF_11') | ~m1_subset_1(E_1417, k1_zfmisc_1(k2_zfmisc_1(A_1415, B_1416))))), inference(resolution, [status(thm)], [c_36, c_7724])).
% 10.68/4.09  tff(c_8195, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_38, c_8177])).
% 10.68/4.09  tff(c_7850, plain, (![A_1367, B_1368, E_1369]: (k4_relset_1(A_1367, B_1368, '#skF_8', '#skF_9', E_1369, '#skF_11')=k5_relat_1(E_1369, '#skF_11') | ~m1_subset_1(E_1369, k1_zfmisc_1(k2_zfmisc_1(A_1367, B_1368))))), inference(resolution, [status(thm)], [c_36, c_7724])).
% 10.68/4.09  tff(c_7868, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_38, c_7850])).
% 10.68/4.09  tff(c_60, plain, (m1_subset_1('#skF_14', '#skF_8') | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_71, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_60])).
% 10.68/4.09  tff(c_7825, plain, (![A_1363, D_1366, F_1365, E_1362, B_1364]: (r2_hidden(k4_tarski(D_1366, E_1362), k5_relat_1(A_1363, B_1364)) | ~r2_hidden(k4_tarski(F_1365, E_1362), B_1364) | ~r2_hidden(k4_tarski(D_1366, F_1365), A_1363) | ~v1_relat_1(k5_relat_1(A_1363, B_1364)) | ~v1_relat_1(B_1364) | ~v1_relat_1(A_1363))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_7847, plain, (![D_1366, A_1363]: (r2_hidden(k4_tarski(D_1366, '#skF_16'), k5_relat_1(A_1363, k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_1366, '#skF_15'), A_1363) | ~v1_relat_1(k5_relat_1(A_1363, k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))) | ~v1_relat_1(k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')) | ~v1_relat_1(A_1363))), inference(resolution, [status(thm)], [c_71, c_7825])).
% 10.68/4.09  tff(c_7954, plain, (![D_1366, A_1363]: (r2_hidden(k4_tarski(D_1366, '#skF_16'), k5_relat_1(A_1363, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_1366, '#skF_15'), A_1363) | ~v1_relat_1(k5_relat_1(A_1363, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_1363))), inference(demodulation, [status(thm), theory('equality')], [c_7868, c_7868, c_7868, c_7847])).
% 10.68/4.09  tff(c_7955, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_7954])).
% 10.68/4.09  tff(c_7958, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_7955])).
% 10.68/4.09  tff(c_7962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_7958])).
% 10.68/4.09  tff(c_7964, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_7954])).
% 10.68/4.09  tff(c_1592, plain, (![B_606, D_608, E_603, F_604, A_607, C_605]: (k4_relset_1(A_607, B_606, C_605, D_608, E_603, F_604)=k5_relat_1(E_603, F_604) | ~m1_subset_1(F_604, k1_zfmisc_1(k2_zfmisc_1(C_605, D_608))) | ~m1_subset_1(E_603, k1_zfmisc_1(k2_zfmisc_1(A_607, B_606))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.68/4.09  tff(c_1599, plain, (![A_609, B_610, E_611]: (k4_relset_1(A_609, B_610, '#skF_8', '#skF_9', E_611, '#skF_11')=k5_relat_1(E_611, '#skF_11') | ~m1_subset_1(E_611, k1_zfmisc_1(k2_zfmisc_1(A_609, B_610))))), inference(resolution, [status(thm)], [c_36, c_1592])).
% 10.68/4.09  tff(c_1607, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_38, c_1599])).
% 10.68/4.09  tff(c_1614, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1607, c_71])).
% 10.68/4.09  tff(c_1648, plain, (![E_616, A_617, F_619, D_620, B_618]: (r2_hidden(k4_tarski(D_620, E_616), k5_relat_1(A_617, B_618)) | ~r2_hidden(k4_tarski(F_619, E_616), B_618) | ~r2_hidden(k4_tarski(D_620, F_619), A_617) | ~v1_relat_1(k5_relat_1(A_617, B_618)) | ~v1_relat_1(B_618) | ~v1_relat_1(A_617))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_1653, plain, (![D_620, A_617]: (r2_hidden(k4_tarski(D_620, '#skF_16'), k5_relat_1(A_617, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_620, '#skF_15'), A_617) | ~v1_relat_1(k5_relat_1(A_617, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_617))), inference(resolution, [status(thm)], [c_1614, c_1648])).
% 10.68/4.09  tff(c_1655, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_1653])).
% 10.68/4.09  tff(c_1658, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_1655])).
% 10.68/4.09  tff(c_1662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_1658])).
% 10.68/4.09  tff(c_1664, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_1653])).
% 10.68/4.09  tff(c_1727, plain, (![E_641, A_642, B_643, D_644]: (r2_hidden(k4_tarski('#skF_1'(E_641, k5_relat_1(A_642, B_643), A_642, B_643, D_644), E_641), B_643) | ~r2_hidden(k4_tarski(D_644, E_641), k5_relat_1(A_642, B_643)) | ~v1_relat_1(k5_relat_1(A_642, B_643)) | ~v1_relat_1(B_643) | ~v1_relat_1(A_642))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.68/4.09  tff(c_1813, plain, (![B_660, D_658, E_661, A_659, A_662]: (r2_hidden(k4_tarski('#skF_1'(E_661, k5_relat_1(A_662, B_660), A_662, B_660, D_658), E_661), A_659) | ~m1_subset_1(B_660, k1_zfmisc_1(A_659)) | ~r2_hidden(k4_tarski(D_658, E_661), k5_relat_1(A_662, B_660)) | ~v1_relat_1(k5_relat_1(A_662, B_660)) | ~v1_relat_1(B_660) | ~v1_relat_1(A_662))), inference(resolution, [status(thm)], [c_1727, c_8])).
% 10.68/4.09  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.68/4.09  tff(c_2897, plain, (![D_819, E_822, B_817, A_818, C_820, D_821]: (r2_hidden('#skF_1'(E_822, k5_relat_1(A_818, B_817), A_818, B_817, D_821), C_820) | ~m1_subset_1(B_817, k1_zfmisc_1(k2_zfmisc_1(C_820, D_819))) | ~r2_hidden(k4_tarski(D_821, E_822), k5_relat_1(A_818, B_817)) | ~v1_relat_1(k5_relat_1(A_818, B_817)) | ~v1_relat_1(B_817) | ~v1_relat_1(A_818))), inference(resolution, [status(thm)], [c_1813, c_6])).
% 10.68/4.09  tff(c_2911, plain, (![E_822, A_818, D_821]: (r2_hidden('#skF_1'(E_822, k5_relat_1(A_818, '#skF_11'), A_818, '#skF_11', D_821), '#skF_8') | ~r2_hidden(k4_tarski(D_821, E_822), k5_relat_1(A_818, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_818, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_818))), inference(resolution, [status(thm)], [c_36, c_2897])).
% 10.68/4.09  tff(c_2924, plain, (![E_823, A_824, D_825]: (r2_hidden('#skF_1'(E_823, k5_relat_1(A_824, '#skF_11'), A_824, '#skF_11', D_825), '#skF_8') | ~r2_hidden(k4_tarski(D_825, E_823), k5_relat_1(A_824, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_824, '#skF_11')) | ~v1_relat_1(A_824))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2911])).
% 10.68/4.09  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.68/4.09  tff(c_2940, plain, (![E_829, A_830, D_831]: (m1_subset_1('#skF_1'(E_829, k5_relat_1(A_830, '#skF_11'), A_830, '#skF_11', D_831), '#skF_8') | ~r2_hidden(k4_tarski(D_831, E_829), k5_relat_1(A_830, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_830, '#skF_11')) | ~v1_relat_1(A_830))), inference(resolution, [status(thm)], [c_2924, c_10])).
% 10.68/4.09  tff(c_2969, plain, (m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1614, c_2940])).
% 10.68/4.09  tff(c_2981, plain, (m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1664, c_2969])).
% 10.68/4.09  tff(c_28, plain, (![D_102, E_103, A_11, B_63]: (r2_hidden(k4_tarski(D_102, '#skF_1'(E_103, k5_relat_1(A_11, B_63), A_11, B_63, D_102)), A_11) | ~r2_hidden(k4_tarski(D_102, E_103), k5_relat_1(A_11, B_63)) | ~v1_relat_1(k5_relat_1(A_11, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_50, plain, (![H_335]: (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | ~r2_hidden(k4_tarski(H_335, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_335), '#skF_10') | ~m1_subset_1(H_335, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_1590, plain, (![H_335]: (~r2_hidden(k4_tarski(H_335, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_335), '#skF_10') | ~m1_subset_1(H_335, '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 10.68/4.09  tff(c_1738, plain, (![A_642, D_644]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'('#skF_16', k5_relat_1(A_642, '#skF_11'), A_642, '#skF_11', D_644)), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_16', k5_relat_1(A_642, '#skF_11'), A_642, '#skF_11', D_644), '#skF_8') | ~r2_hidden(k4_tarski(D_644, '#skF_16'), k5_relat_1(A_642, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_642, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_642))), inference(resolution, [status(thm)], [c_1727, c_1590])).
% 10.68/4.09  tff(c_5215, plain, (![A_1011, D_1012]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'('#skF_16', k5_relat_1(A_1011, '#skF_11'), A_1011, '#skF_11', D_1012)), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_16', k5_relat_1(A_1011, '#skF_11'), A_1011, '#skF_11', D_1012), '#skF_8') | ~r2_hidden(k4_tarski(D_1012, '#skF_16'), k5_relat_1(A_1011, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1011, '#skF_11')) | ~v1_relat_1(A_1011))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1738])).
% 10.68/4.09  tff(c_5223, plain, (~m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_28, c_5215])).
% 10.68/4.09  tff(c_5230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_1664, c_1614, c_2981, c_5223])).
% 10.68/4.09  tff(c_5231, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10')), inference(splitRight, [status(thm)], [c_50])).
% 10.68/4.09  tff(c_5309, plain, (![B_1029, D_1031, C_1028, F_1027, E_1026, A_1030]: (k4_relset_1(A_1030, B_1029, C_1028, D_1031, E_1026, F_1027)=k5_relat_1(E_1026, F_1027) | ~m1_subset_1(F_1027, k1_zfmisc_1(k2_zfmisc_1(C_1028, D_1031))) | ~m1_subset_1(E_1026, k1_zfmisc_1(k2_zfmisc_1(A_1030, B_1029))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.68/4.09  tff(c_5320, plain, (![A_1032, B_1033, E_1034]: (k4_relset_1(A_1032, B_1033, '#skF_8', '#skF_9', E_1034, '#skF_11')=k5_relat_1(E_1034, '#skF_11') | ~m1_subset_1(E_1034, k1_zfmisc_1(k2_zfmisc_1(A_1032, B_1033))))), inference(resolution, [status(thm)], [c_36, c_5309])).
% 10.68/4.09  tff(c_5333, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_38, c_5320])).
% 10.68/4.09  tff(c_5340, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_5333, c_71])).
% 10.68/4.09  tff(c_5375, plain, (![D_1042, E_1038, F_1041, A_1039, B_1040]: (r2_hidden(k4_tarski(D_1042, E_1038), k5_relat_1(A_1039, B_1040)) | ~r2_hidden(k4_tarski(F_1041, E_1038), B_1040) | ~r2_hidden(k4_tarski(D_1042, F_1041), A_1039) | ~v1_relat_1(k5_relat_1(A_1039, B_1040)) | ~v1_relat_1(B_1040) | ~v1_relat_1(A_1039))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_5384, plain, (![D_1042, A_1039]: (r2_hidden(k4_tarski(D_1042, '#skF_16'), k5_relat_1(A_1039, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_1042, '#skF_15'), A_1039) | ~v1_relat_1(k5_relat_1(A_1039, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_1039))), inference(resolution, [status(thm)], [c_5340, c_5375])).
% 10.68/4.09  tff(c_5416, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_5384])).
% 10.68/4.09  tff(c_5419, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_5416])).
% 10.68/4.09  tff(c_5423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_5419])).
% 10.68/4.09  tff(c_5425, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_5384])).
% 10.68/4.09  tff(c_5484, plain, (![D_1078, E_1079, A_1080, B_1081]: (r2_hidden(k4_tarski(D_1078, '#skF_1'(E_1079, k5_relat_1(A_1080, B_1081), A_1080, B_1081, D_1078)), A_1080) | ~r2_hidden(k4_tarski(D_1078, E_1079), k5_relat_1(A_1080, B_1081)) | ~v1_relat_1(k5_relat_1(A_1080, B_1081)) | ~v1_relat_1(B_1081) | ~v1_relat_1(A_1080))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_5426, plain, (![E_1057, A_1058, B_1059, D_1060]: (r2_hidden(k4_tarski('#skF_1'(E_1057, k5_relat_1(A_1058, B_1059), A_1058, B_1059, D_1060), E_1057), B_1059) | ~r2_hidden(k4_tarski(D_1060, E_1057), k5_relat_1(A_1058, B_1059)) | ~v1_relat_1(k5_relat_1(A_1058, B_1059)) | ~v1_relat_1(B_1059) | ~v1_relat_1(A_1058))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_48, plain, (![H_335]: (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11') | ~r2_hidden(k4_tarski(H_335, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_335), '#skF_10') | ~m1_subset_1(H_335, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_5262, plain, (![H_335]: (~r2_hidden(k4_tarski(H_335, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_335), '#skF_10') | ~m1_subset_1(H_335, '#skF_8'))), inference(splitLeft, [status(thm)], [c_48])).
% 10.68/4.09  tff(c_5431, plain, (![A_1058, D_1060]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'('#skF_16', k5_relat_1(A_1058, '#skF_11'), A_1058, '#skF_11', D_1060)), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_16', k5_relat_1(A_1058, '#skF_11'), A_1058, '#skF_11', D_1060), '#skF_8') | ~r2_hidden(k4_tarski(D_1060, '#skF_16'), k5_relat_1(A_1058, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1058, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1058))), inference(resolution, [status(thm)], [c_5426, c_5262])).
% 10.68/4.09  tff(c_5448, plain, (![A_1058, D_1060]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'('#skF_16', k5_relat_1(A_1058, '#skF_11'), A_1058, '#skF_11', D_1060)), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_16', k5_relat_1(A_1058, '#skF_11'), A_1058, '#skF_11', D_1060), '#skF_8') | ~r2_hidden(k4_tarski(D_1060, '#skF_16'), k5_relat_1(A_1058, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1058, '#skF_11')) | ~v1_relat_1(A_1058))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_5431])).
% 10.68/4.09  tff(c_5492, plain, (~m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_5484, c_5448])).
% 10.68/4.09  tff(c_5511, plain, (~m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_5425, c_5340, c_5492])).
% 10.68/4.09  tff(c_6530, plain, (![A_1231, A_1235, B_1232, E_1234, D_1233]: (r2_hidden(k4_tarski('#skF_1'(E_1234, k5_relat_1(A_1231, B_1232), A_1231, B_1232, D_1233), E_1234), A_1235) | ~m1_subset_1(B_1232, k1_zfmisc_1(A_1235)) | ~r2_hidden(k4_tarski(D_1233, E_1234), k5_relat_1(A_1231, B_1232)) | ~v1_relat_1(k5_relat_1(A_1231, B_1232)) | ~v1_relat_1(B_1232) | ~v1_relat_1(A_1231))), inference(resolution, [status(thm)], [c_5426, c_8])).
% 10.68/4.09  tff(c_7441, plain, (![B_1317, A_1318, D_1319, C_1320, D_1322, E_1321]: (r2_hidden('#skF_1'(E_1321, k5_relat_1(A_1318, B_1317), A_1318, B_1317, D_1322), C_1320) | ~m1_subset_1(B_1317, k1_zfmisc_1(k2_zfmisc_1(C_1320, D_1319))) | ~r2_hidden(k4_tarski(D_1322, E_1321), k5_relat_1(A_1318, B_1317)) | ~v1_relat_1(k5_relat_1(A_1318, B_1317)) | ~v1_relat_1(B_1317) | ~v1_relat_1(A_1318))), inference(resolution, [status(thm)], [c_6530, c_6])).
% 10.68/4.09  tff(c_7461, plain, (![E_1321, A_1318, D_1322]: (r2_hidden('#skF_1'(E_1321, k5_relat_1(A_1318, '#skF_11'), A_1318, '#skF_11', D_1322), '#skF_8') | ~r2_hidden(k4_tarski(D_1322, E_1321), k5_relat_1(A_1318, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1318, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1318))), inference(resolution, [status(thm)], [c_36, c_7441])).
% 10.68/4.09  tff(c_7476, plain, (![E_1323, A_1324, D_1325]: (r2_hidden('#skF_1'(E_1323, k5_relat_1(A_1324, '#skF_11'), A_1324, '#skF_11', D_1325), '#skF_8') | ~r2_hidden(k4_tarski(D_1325, E_1323), k5_relat_1(A_1324, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1324, '#skF_11')) | ~v1_relat_1(A_1324))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_7461])).
% 10.68/4.09  tff(c_7614, plain, (![E_1332, A_1333, D_1334]: (m1_subset_1('#skF_1'(E_1332, k5_relat_1(A_1333, '#skF_11'), A_1333, '#skF_11', D_1334), '#skF_8') | ~r2_hidden(k4_tarski(D_1334, E_1332), k5_relat_1(A_1333, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1333, '#skF_11')) | ~v1_relat_1(A_1333))), inference(resolution, [status(thm)], [c_7476, c_10])).
% 10.68/4.09  tff(c_7658, plain, (m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_5340, c_7614])).
% 10.68/4.09  tff(c_7680, plain, (m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5425, c_7658])).
% 10.68/4.09  tff(c_7682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5511, c_7680])).
% 10.68/4.09  tff(c_7683, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11')), inference(splitRight, [status(thm)], [c_48])).
% 10.68/4.09  tff(c_7829, plain, (![D_1366, A_1363]: (r2_hidden(k4_tarski(D_1366, '#skF_13'), k5_relat_1(A_1363, '#skF_11')) | ~r2_hidden(k4_tarski(D_1366, '#skF_14'), A_1363) | ~v1_relat_1(k5_relat_1(A_1363, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1363))), inference(resolution, [status(thm)], [c_7683, c_7825])).
% 10.68/4.09  tff(c_8008, plain, (![D_1384, A_1385]: (r2_hidden(k4_tarski(D_1384, '#skF_13'), k5_relat_1(A_1385, '#skF_11')) | ~r2_hidden(k4_tarski(D_1384, '#skF_14'), A_1385) | ~v1_relat_1(k5_relat_1(A_1385, '#skF_11')) | ~v1_relat_1(A_1385))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_7829])).
% 10.68/4.09  tff(c_46, plain, (![H_335]: (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')) | ~r2_hidden(k4_tarski(H_335, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_335), '#skF_10') | ~m1_subset_1(H_335, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_7747, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_46])).
% 10.68/4.09  tff(c_7873, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_7868, c_7747])).
% 10.68/4.09  tff(c_8011, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_8008, c_7873])).
% 10.68/4.09  tff(c_8022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_7964, c_5231, c_8011])).
% 10.68/4.09  tff(c_8024, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_46])).
% 10.68/4.09  tff(c_8095, plain, (![D_1405, B_1403, E_1401, F_1404, A_1402]: (r2_hidden(k4_tarski(D_1405, E_1401), k5_relat_1(A_1402, B_1403)) | ~r2_hidden(k4_tarski(F_1404, E_1401), B_1403) | ~r2_hidden(k4_tarski(D_1405, F_1404), A_1402) | ~v1_relat_1(k5_relat_1(A_1402, B_1403)) | ~v1_relat_1(B_1403) | ~v1_relat_1(A_1402))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_8110, plain, (![D_1405, A_1402]: (r2_hidden(k4_tarski(D_1405, '#skF_13'), k5_relat_1(A_1402, k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_1405, '#skF_12'), A_1402) | ~v1_relat_1(k5_relat_1(A_1402, k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))) | ~v1_relat_1(k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')) | ~v1_relat_1(A_1402))), inference(resolution, [status(thm)], [c_8024, c_8095])).
% 10.68/4.09  tff(c_8389, plain, (![D_1405, A_1402]: (r2_hidden(k4_tarski(D_1405, '#skF_13'), k5_relat_1(A_1402, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_1405, '#skF_12'), A_1402) | ~v1_relat_1(k5_relat_1(A_1402, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_1402))), inference(demodulation, [status(thm), theory('equality')], [c_8195, c_8195, c_8195, c_8110])).
% 10.68/4.09  tff(c_8390, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_8389])).
% 10.68/4.09  tff(c_8393, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_8390])).
% 10.68/4.09  tff(c_8397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_8393])).
% 10.68/4.09  tff(c_8399, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_8389])).
% 10.68/4.09  tff(c_8205, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_8195, c_71])).
% 10.68/4.09  tff(c_8232, plain, (![E_1418, A_1419, B_1420, D_1421]: (r2_hidden(k4_tarski('#skF_1'(E_1418, k5_relat_1(A_1419, B_1420), A_1419, B_1420, D_1421), E_1418), B_1420) | ~r2_hidden(k4_tarski(D_1421, E_1418), k5_relat_1(A_1419, B_1420)) | ~v1_relat_1(k5_relat_1(A_1419, B_1420)) | ~v1_relat_1(B_1420) | ~v1_relat_1(A_1419))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_8023, plain, (![H_335]: (~r2_hidden(k4_tarski(H_335, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_335), '#skF_10') | ~m1_subset_1(H_335, '#skF_8'))), inference(splitRight, [status(thm)], [c_46])).
% 10.68/4.09  tff(c_8237, plain, (![A_1419, D_1421]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'('#skF_16', k5_relat_1(A_1419, '#skF_11'), A_1419, '#skF_11', D_1421)), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_16', k5_relat_1(A_1419, '#skF_11'), A_1419, '#skF_11', D_1421), '#skF_8') | ~r2_hidden(k4_tarski(D_1421, '#skF_16'), k5_relat_1(A_1419, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1419, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1419))), inference(resolution, [status(thm)], [c_8232, c_8023])).
% 10.68/4.09  tff(c_10942, plain, (![A_1722, D_1723]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'('#skF_16', k5_relat_1(A_1722, '#skF_11'), A_1722, '#skF_11', D_1723)), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_16', k5_relat_1(A_1722, '#skF_11'), A_1722, '#skF_11', D_1723), '#skF_8') | ~r2_hidden(k4_tarski(D_1723, '#skF_16'), k5_relat_1(A_1722, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1722, '#skF_11')) | ~v1_relat_1(A_1722))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_8237])).
% 10.68/4.09  tff(c_10950, plain, (~m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_28, c_10942])).
% 10.68/4.09  tff(c_10956, plain, (~m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_8399, c_8205, c_10950])).
% 10.68/4.09  tff(c_8714, plain, (![E_1526, A_1528, A_1530, D_1527, B_1529]: (r2_hidden(k4_tarski('#skF_1'(E_1526, k5_relat_1(A_1528, B_1529), A_1528, B_1529, D_1527), E_1526), A_1530) | ~m1_subset_1(B_1529, k1_zfmisc_1(A_1530)) | ~r2_hidden(k4_tarski(D_1527, E_1526), k5_relat_1(A_1528, B_1529)) | ~v1_relat_1(k5_relat_1(A_1528, B_1529)) | ~v1_relat_1(B_1529) | ~v1_relat_1(A_1528))), inference(resolution, [status(thm)], [c_8232, c_8])).
% 10.68/4.09  tff(c_12224, plain, (![A_1864, E_1859, B_1863, D_1861, D_1860, C_1862]: (r2_hidden('#skF_1'(E_1859, k5_relat_1(A_1864, B_1863), A_1864, B_1863, D_1861), C_1862) | ~m1_subset_1(B_1863, k1_zfmisc_1(k2_zfmisc_1(C_1862, D_1860))) | ~r2_hidden(k4_tarski(D_1861, E_1859), k5_relat_1(A_1864, B_1863)) | ~v1_relat_1(k5_relat_1(A_1864, B_1863)) | ~v1_relat_1(B_1863) | ~v1_relat_1(A_1864))), inference(resolution, [status(thm)], [c_8714, c_6])).
% 10.68/4.09  tff(c_12259, plain, (![E_1859, A_1864, D_1861]: (r2_hidden('#skF_1'(E_1859, k5_relat_1(A_1864, '#skF_11'), A_1864, '#skF_11', D_1861), '#skF_8') | ~r2_hidden(k4_tarski(D_1861, E_1859), k5_relat_1(A_1864, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1864, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1864))), inference(resolution, [status(thm)], [c_36, c_12224])).
% 10.68/4.09  tff(c_12279, plain, (![E_1865, A_1866, D_1867]: (r2_hidden('#skF_1'(E_1865, k5_relat_1(A_1866, '#skF_11'), A_1866, '#skF_11', D_1867), '#skF_8') | ~r2_hidden(k4_tarski(D_1867, E_1865), k5_relat_1(A_1866, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1866, '#skF_11')) | ~v1_relat_1(A_1866))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12259])).
% 10.68/4.09  tff(c_12450, plain, (![E_1875, A_1876, D_1877]: (m1_subset_1('#skF_1'(E_1875, k5_relat_1(A_1876, '#skF_11'), A_1876, '#skF_11', D_1877), '#skF_8') | ~r2_hidden(k4_tarski(D_1877, E_1875), k5_relat_1(A_1876, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1876, '#skF_11')) | ~v1_relat_1(A_1876))), inference(resolution, [status(thm)], [c_12279, c_10])).
% 10.68/4.09  tff(c_12534, plain, (m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_8205, c_12450])).
% 10.68/4.09  tff(c_12580, plain, (m1_subset_1('#skF_1'('#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_10', '#skF_11', '#skF_15'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8399, c_12534])).
% 10.68/4.09  tff(c_12582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10956, c_12580])).
% 10.68/4.09  tff(c_12584, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_60])).
% 10.68/4.09  tff(c_58, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_12585, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_58])).
% 10.68/4.09  tff(c_12590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12584, c_12585])).
% 10.68/4.09  tff(c_12591, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10')), inference(splitRight, [status(thm)], [c_58])).
% 10.68/4.09  tff(c_12592, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_58])).
% 10.68/4.09  tff(c_56, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11') | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_12598, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_56])).
% 10.68/4.09  tff(c_12657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12592, c_12598])).
% 10.68/4.09  tff(c_12658, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11')), inference(splitRight, [status(thm)], [c_56])).
% 10.68/4.09  tff(c_12870, plain, (![B_1965, F_1966, E_1963, D_1967, A_1964]: (r2_hidden(k4_tarski(D_1967, E_1963), k5_relat_1(A_1964, B_1965)) | ~r2_hidden(k4_tarski(F_1966, E_1963), B_1965) | ~r2_hidden(k4_tarski(D_1967, F_1966), A_1964) | ~v1_relat_1(k5_relat_1(A_1964, B_1965)) | ~v1_relat_1(B_1965) | ~v1_relat_1(A_1964))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.68/4.09  tff(c_12878, plain, (![D_1967, A_1964]: (r2_hidden(k4_tarski(D_1967, '#skF_13'), k5_relat_1(A_1964, '#skF_11')) | ~r2_hidden(k4_tarski(D_1967, '#skF_14'), A_1964) | ~v1_relat_1(k5_relat_1(A_1964, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1964))), inference(resolution, [status(thm)], [c_12658, c_12870])).
% 10.68/4.09  tff(c_12954, plain, (![D_1982, A_1983]: (r2_hidden(k4_tarski(D_1982, '#skF_13'), k5_relat_1(A_1983, '#skF_11')) | ~r2_hidden(k4_tarski(D_1982, '#skF_14'), A_1983) | ~v1_relat_1(k5_relat_1(A_1983, '#skF_11')) | ~v1_relat_1(A_1983))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12878])).
% 10.68/4.09  tff(c_12809, plain, (![F_1953, E_1952, D_1957, C_1954, A_1956, B_1955]: (k4_relset_1(A_1956, B_1955, C_1954, D_1957, E_1952, F_1953)=k5_relat_1(E_1952, F_1953) | ~m1_subset_1(F_1953, k1_zfmisc_1(k2_zfmisc_1(C_1954, D_1957))) | ~m1_subset_1(E_1952, k1_zfmisc_1(k2_zfmisc_1(A_1956, B_1955))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.68/4.09  tff(c_12841, plain, (![A_1960, B_1961, E_1962]: (k4_relset_1(A_1960, B_1961, '#skF_8', '#skF_9', E_1962, '#skF_11')=k5_relat_1(E_1962, '#skF_11') | ~m1_subset_1(E_1962, k1_zfmisc_1(k2_zfmisc_1(A_1960, B_1961))))), inference(resolution, [status(thm)], [c_36, c_12809])).
% 10.68/4.09  tff(c_12859, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_38, c_12841])).
% 10.68/4.09  tff(c_12659, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_56])).
% 10.68/4.09  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')) | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.09  tff(c_12791, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_12659, c_54])).
% 10.68/4.09  tff(c_12864, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_12859, c_12791])).
% 10.68/4.09  tff(c_12957, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_12954, c_12864])).
% 10.68/4.09  tff(c_12967, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12591, c_12957])).
% 10.68/4.09  tff(c_12973, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_12967])).
% 10.68/4.09  tff(c_12977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_12973])).
% 10.68/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/4.09  
% 10.68/4.09  Inference rules
% 10.68/4.09  ----------------------
% 10.68/4.09  #Ref     : 0
% 10.68/4.09  #Sup     : 2789
% 10.68/4.09  #Fact    : 0
% 10.68/4.09  #Define  : 0
% 10.68/4.09  #Split   : 83
% 10.68/4.09  #Chain   : 0
% 10.68/4.09  #Close   : 0
% 10.68/4.09  
% 10.68/4.09  Ordering : KBO
% 10.68/4.09  
% 10.68/4.09  Simplification rules
% 10.68/4.09  ----------------------
% 10.68/4.09  #Subsume      : 183
% 10.68/4.09  #Demod        : 440
% 10.68/4.09  #Tautology    : 152
% 10.68/4.09  #SimpNegUnit  : 6
% 10.68/4.09  #BackRed      : 21
% 10.68/4.09  
% 10.68/4.09  #Partial instantiations: 0
% 10.68/4.09  #Strategies tried      : 1
% 10.68/4.09  
% 10.68/4.09  Timing (in seconds)
% 10.68/4.09  ----------------------
% 10.68/4.10  Preprocessing        : 0.35
% 10.68/4.10  Parsing              : 0.17
% 10.68/4.10  CNF conversion       : 0.05
% 10.68/4.10  Main loop            : 2.92
% 10.68/4.10  Inferencing          : 0.99
% 10.68/4.10  Reduction            : 0.79
% 10.68/4.10  Demodulation         : 0.55
% 10.68/4.10  BG Simplification    : 0.12
% 10.68/4.10  Subsumption          : 0.77
% 10.68/4.10  Abstraction          : 0.20
% 10.68/4.10  MUC search           : 0.00
% 10.68/4.10  Cooper               : 0.00
% 10.68/4.10  Total                : 3.35
% 10.68/4.10  Index Insertion      : 0.00
% 10.68/4.10  Index Deletion       : 0.00
% 10.68/4.10  Index Matching       : 0.00
% 10.68/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
