%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:12 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 449 expanded)
%              Number of leaves         :   32 ( 155 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 (1232 expanded)
%              Number of equality atoms :   93 ( 387 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_40,C_41,B_42] :
      ( r2_hidden(k2_mcart_1(A_40),C_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1065,plain,(
    ! [B_223,C_224] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_223,C_224))),C_224)
      | v1_xboole_0(k2_zfmisc_1(B_223,C_224)) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_45,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_81,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_75,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_45,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_66])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_26,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_458,plain,(
    ! [A_114,B_115,C_116] : k2_zfmisc_1(k2_zfmisc_1(A_114,B_115),C_116) = k3_zfmisc_1(A_114,B_115,C_116) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_14,C_16,B_15] :
      ( r2_hidden(k2_mcart_1(A_14),C_16)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_477,plain,(
    ! [A_117,C_118,A_119,B_120] :
      ( r2_hidden(k2_mcart_1(A_117),C_118)
      | ~ r2_hidden(A_117,k3_zfmisc_1(A_119,B_120,C_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_14])).

tff(c_483,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_477])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_74,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_45,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_66])).

tff(c_456,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_493,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_mcart_1(A_121,B_122,C_123,D_124) = k2_mcart_1(D_124)
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_497,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_493])).

tff(c_523,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_497])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [B_37,A_38] :
      ( ~ r1_tarski(B_37,A_38)
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_39] :
      ( ~ r1_tarski(A_39,'#skF_1'(A_39))
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_4,c_42])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_525,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_60])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_525])).

tff(c_529,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_497])).

tff(c_591,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_76,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k1_mcart_1(A_46),B_47)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_401,plain,(
    ! [B_106,C_107] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_106,C_107))),B_106)
      | v1_xboole_0(k2_zfmisc_1(B_106,C_107)) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_24,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_83,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_104,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k7_mcart_1(A_52,B_53,C_54,D_55) = k2_mcart_1(D_55)
      | ~ m1_subset_1(D_55,k3_zfmisc_1(A_52,B_53,C_54))
      | k1_xboole_0 = C_54
      | k1_xboole_0 = B_53
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_104])).

tff(c_125,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_127,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_60])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_127])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_162,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k5_mcart_1(A_64,B_65,C_66,D_67) = k1_mcart_1(k1_mcart_1(D_67))
      | ~ m1_subset_1(D_67,k3_zfmisc_1(A_64,B_65,C_66))
      | k1_xboole_0 = C_66
      | k1_xboole_0 = B_65
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_165,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_168,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_165])).

tff(c_251,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_257,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_60])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_257])).

tff(c_261,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_269,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_85,plain,(
    ! [A_49,B_50,C_51] : k2_zfmisc_1(k2_zfmisc_1(A_49,B_50),C_51) = k3_zfmisc_1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_14),B_15)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_311,plain,(
    ! [A_94,A_95,B_96,C_97] :
      ( r2_hidden(k1_mcart_1(A_94),k2_zfmisc_1(A_95,B_96))
      | ~ r2_hidden(A_94,k3_zfmisc_1(A_95,B_96,C_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_16])).

tff(c_328,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_26,c_311])).

tff(c_331,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_328,c_16])).

tff(c_341,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_331])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_341])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_354,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_60])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_354])).

tff(c_358,plain,(
    ! [A_45] : ~ r2_hidden(A_45,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_425,plain,(
    ! [C_107] : v1_xboole_0(k2_zfmisc_1('#skF_5',C_107)) ),
    inference(resolution,[status(thm)],[c_401,c_358])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_434,plain,(
    ! [B_109,C_110] :
      ( ~ v1_xboole_0(B_109)
      | v1_xboole_0(k2_zfmisc_1(B_109,C_110)) ) ),
    inference(resolution,[status(thm)],[c_401,c_2])).

tff(c_438,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_111,B_112))
      | v1_xboole_0(k3_zfmisc_1(A_111,B_112,C_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_434])).

tff(c_54,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_441,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_438,c_54])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_441])).

tff(c_446,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_457,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_592,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_457])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_592])).

tff(c_596,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_598,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_602,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_60])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_602])).

tff(c_606,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_620,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_60])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_620])).

tff(c_624,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_661,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k7_mcart_1(A_154,B_155,C_156,D_157) = k2_mcart_1(D_157)
      | ~ m1_subset_1(D_157,k3_zfmisc_1(A_154,B_155,C_156))
      | k1_xboole_0 = C_156
      | k1_xboole_0 = B_155
      | k1_xboole_0 = A_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_665,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_661])).

tff(c_701,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_703,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_60])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_703])).

tff(c_708,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_796,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k5_mcart_1(A_181,B_182,C_183,D_184) = k1_mcart_1(k1_mcart_1(D_184))
      | ~ m1_subset_1(D_184,k3_zfmisc_1(A_181,B_182,C_183))
      | k1_xboole_0 = C_183
      | k1_xboole_0 = B_182
      | k1_xboole_0 = A_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_799,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_796])).

tff(c_802,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_799])).

tff(c_845,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_853,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_60])).

tff(c_856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_853])).

tff(c_858,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_722,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k6_mcart_1(A_165,B_166,C_167,D_168) = k2_mcart_1(k1_mcart_1(D_168))
      | ~ m1_subset_1(D_168,k3_zfmisc_1(A_165,B_166,C_167))
      | k1_xboole_0 = C_167
      | k1_xboole_0 = B_166
      | k1_xboole_0 = A_165 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_725,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_722])).

tff(c_728,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_725])).

tff(c_907,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_858,c_728])).

tff(c_908,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_907])).

tff(c_917,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_60])).

tff(c_920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_917])).

tff(c_921,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_634,plain,(
    ! [A_147,B_148,C_149] : k2_zfmisc_1(k2_zfmisc_1(A_147,B_148),C_149) = k3_zfmisc_1(A_147,B_148,C_149) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_865,plain,(
    ! [A_192,A_193,B_194,C_195] :
      ( r2_hidden(k1_mcart_1(A_192),k2_zfmisc_1(A_193,B_194))
      | ~ r2_hidden(A_192,k3_zfmisc_1(A_193,B_194,C_195)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_16])).

tff(c_882,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_26,c_865])).

tff(c_896,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_882,c_14])).

tff(c_924,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_896])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_924])).

tff(c_927,plain,(
    ! [A_45] : ~ r2_hidden(A_45,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_447,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_927,c_447])).

tff(c_950,plain,(
    ! [A_45] : ~ r2_hidden(A_45,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_1089,plain,(
    ! [B_223] : v1_xboole_0(k2_zfmisc_1(B_223,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_1065,c_950])).

tff(c_1007,plain,(
    ! [B_211,C_212] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_211,C_212))),B_211)
      | v1_xboole_0(k2_zfmisc_1(B_211,C_212)) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_1040,plain,(
    ! [B_214,C_215] :
      ( ~ v1_xboole_0(B_214)
      | v1_xboole_0(k2_zfmisc_1(B_214,C_215)) ) ),
    inference(resolution,[status(thm)],[c_1007,c_2])).

tff(c_1051,plain,(
    ! [A_220,B_221,C_222] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_220,B_221))
      | v1_xboole_0(k3_zfmisc_1(A_220,B_221,C_222)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1040])).

tff(c_1055,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1051,c_54])).

tff(c_1097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1055])).

tff(c_1098,plain,(
    ! [A_45] : ~ r2_hidden(A_45,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_1106,plain,(
    ! [A_226,B_227,C_228] : k2_zfmisc_1(k2_zfmisc_1(A_226,B_227),C_228) = k3_zfmisc_1(A_226,B_227,C_228) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1127,plain,(
    ! [A_229,C_230,A_231,B_232] :
      ( r2_hidden(k2_mcart_1(A_229),C_230)
      | ~ r2_hidden(A_229,k3_zfmisc_1(A_231,B_232,C_230)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_14])).

tff(c_1129,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_1127])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_1129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:50:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.52  
% 3.19/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.19/1.53  
% 3.19/1.53  %Foreground sorts:
% 3.19/1.53  
% 3.19/1.53  
% 3.19/1.53  %Background operators:
% 3.19/1.53  
% 3.19/1.53  
% 3.19/1.53  %Foreground operators:
% 3.19/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.53  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.19/1.53  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.19/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.19/1.53  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.19/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.19/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.53  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.19/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.19/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.53  
% 3.23/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.23/1.55  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.23/1.55  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 3.23/1.55  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.23/1.55  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.23/1.55  tff(f_73, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.23/1.55  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.55  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.23/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.55  tff(c_61, plain, (![A_40, C_41, B_42]: (r2_hidden(k2_mcart_1(A_40), C_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_42, C_41)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.55  tff(c_1065, plain, (![B_223, C_224]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_223, C_224))), C_224) | v1_xboole_0(k2_zfmisc_1(B_223, C_224)))), inference(resolution, [status(thm)], [c_4, c_61])).
% 3.23/1.55  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.55  tff(c_66, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.55  tff(c_73, plain, (![A_45]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_45, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_66])).
% 3.23/1.55  tff(c_81, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_73])).
% 3.23/1.55  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.55  tff(c_75, plain, (![A_45]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_45, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_66])).
% 3.23/1.55  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_75])).
% 3.23/1.55  tff(c_26, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.55  tff(c_458, plain, (![A_114, B_115, C_116]: (k2_zfmisc_1(k2_zfmisc_1(A_114, B_115), C_116)=k3_zfmisc_1(A_114, B_115, C_116))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_14, plain, (![A_14, C_16, B_15]: (r2_hidden(k2_mcart_1(A_14), C_16) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.55  tff(c_477, plain, (![A_117, C_118, A_119, B_120]: (r2_hidden(k2_mcart_1(A_117), C_118) | ~r2_hidden(A_117, k3_zfmisc_1(A_119, B_120, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_458, c_14])).
% 3.23/1.55  tff(c_483, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_26, c_477])).
% 3.23/1.55  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.55  tff(c_74, plain, (![A_45]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_45, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_66])).
% 3.23/1.55  tff(c_456, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 3.23/1.55  tff(c_28, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.55  tff(c_493, plain, (![A_121, B_122, C_123, D_124]: (k7_mcart_1(A_121, B_122, C_123, D_124)=k2_mcart_1(D_124) | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.55  tff(c_497, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_493])).
% 3.23/1.55  tff(c_523, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_497])).
% 3.23/1.55  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.55  tff(c_42, plain, (![B_37, A_38]: (~r1_tarski(B_37, A_38) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.55  tff(c_55, plain, (![A_39]: (~r1_tarski(A_39, '#skF_1'(A_39)) | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_4, c_42])).
% 3.23/1.55  tff(c_60, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_55])).
% 3.23/1.55  tff(c_525, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_60])).
% 3.23/1.55  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_525])).
% 3.23/1.55  tff(c_529, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_497])).
% 3.23/1.55  tff(c_591, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_529])).
% 3.23/1.55  tff(c_76, plain, (![A_46, B_47, C_48]: (r2_hidden(k1_mcart_1(A_46), B_47) | ~r2_hidden(A_46, k2_zfmisc_1(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.55  tff(c_401, plain, (![B_106, C_107]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_106, C_107))), B_106) | v1_xboole_0(k2_zfmisc_1(B_106, C_107)))), inference(resolution, [status(thm)], [c_4, c_76])).
% 3.23/1.55  tff(c_24, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.55  tff(c_83, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_24])).
% 3.23/1.55  tff(c_84, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 3.23/1.55  tff(c_104, plain, (![A_52, B_53, C_54, D_55]: (k7_mcart_1(A_52, B_53, C_54, D_55)=k2_mcart_1(D_55) | ~m1_subset_1(D_55, k3_zfmisc_1(A_52, B_53, C_54)) | k1_xboole_0=C_54 | k1_xboole_0=B_53 | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.55  tff(c_108, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_104])).
% 3.23/1.55  tff(c_125, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_108])).
% 3.23/1.55  tff(c_127, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_60])).
% 3.23/1.55  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_127])).
% 3.23/1.55  tff(c_132, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_108])).
% 3.23/1.55  tff(c_162, plain, (![A_64, B_65, C_66, D_67]: (k5_mcart_1(A_64, B_65, C_66, D_67)=k1_mcart_1(k1_mcart_1(D_67)) | ~m1_subset_1(D_67, k3_zfmisc_1(A_64, B_65, C_66)) | k1_xboole_0=C_66 | k1_xboole_0=B_65 | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.55  tff(c_165, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_162])).
% 3.23/1.55  tff(c_168, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_132, c_165])).
% 3.23/1.55  tff(c_251, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_168])).
% 3.23/1.55  tff(c_257, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_60])).
% 3.23/1.55  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_257])).
% 3.23/1.55  tff(c_261, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_168])).
% 3.23/1.55  tff(c_269, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_261])).
% 3.23/1.55  tff(c_85, plain, (![A_49, B_50, C_51]: (k2_zfmisc_1(k2_zfmisc_1(A_49, B_50), C_51)=k3_zfmisc_1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_16, plain, (![A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_14), B_15) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.55  tff(c_311, plain, (![A_94, A_95, B_96, C_97]: (r2_hidden(k1_mcart_1(A_94), k2_zfmisc_1(A_95, B_96)) | ~r2_hidden(A_94, k3_zfmisc_1(A_95, B_96, C_97)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_16])).
% 3.23/1.55  tff(c_328, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_26, c_311])).
% 3.23/1.55  tff(c_331, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_328, c_16])).
% 3.23/1.55  tff(c_341, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_331])).
% 3.23/1.55  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_341])).
% 3.23/1.55  tff(c_344, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_261])).
% 3.23/1.55  tff(c_354, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_60])).
% 3.23/1.55  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_354])).
% 3.23/1.55  tff(c_358, plain, (![A_45]: (~r2_hidden(A_45, '#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 3.23/1.55  tff(c_425, plain, (![C_107]: (v1_xboole_0(k2_zfmisc_1('#skF_5', C_107)))), inference(resolution, [status(thm)], [c_401, c_358])).
% 3.23/1.55  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.55  tff(c_434, plain, (![B_109, C_110]: (~v1_xboole_0(B_109) | v1_xboole_0(k2_zfmisc_1(B_109, C_110)))), inference(resolution, [status(thm)], [c_401, c_2])).
% 3.23/1.55  tff(c_438, plain, (![A_111, B_112, C_113]: (~v1_xboole_0(k2_zfmisc_1(A_111, B_112)) | v1_xboole_0(k3_zfmisc_1(A_111, B_112, C_113)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_434])).
% 3.23/1.55  tff(c_54, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_2])).
% 3.23/1.55  tff(c_441, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_438, c_54])).
% 3.23/1.55  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_425, c_441])).
% 3.23/1.55  tff(c_446, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_24])).
% 3.23/1.55  tff(c_457, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_446])).
% 3.23/1.55  tff(c_592, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_457])).
% 3.23/1.55  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_483, c_592])).
% 3.23/1.55  tff(c_596, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_529])).
% 3.23/1.55  tff(c_598, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_596])).
% 3.23/1.55  tff(c_602, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_60])).
% 3.23/1.55  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_602])).
% 3.23/1.55  tff(c_606, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_596])).
% 3.23/1.55  tff(c_620, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_60])).
% 3.23/1.55  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_620])).
% 3.23/1.55  tff(c_624, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_446])).
% 3.23/1.55  tff(c_661, plain, (![A_154, B_155, C_156, D_157]: (k7_mcart_1(A_154, B_155, C_156, D_157)=k2_mcart_1(D_157) | ~m1_subset_1(D_157, k3_zfmisc_1(A_154, B_155, C_156)) | k1_xboole_0=C_156 | k1_xboole_0=B_155 | k1_xboole_0=A_154)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.55  tff(c_665, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_661])).
% 3.23/1.55  tff(c_701, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_665])).
% 3.23/1.55  tff(c_703, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_701, c_60])).
% 3.23/1.55  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_703])).
% 3.23/1.55  tff(c_708, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_665])).
% 3.23/1.55  tff(c_796, plain, (![A_181, B_182, C_183, D_184]: (k5_mcart_1(A_181, B_182, C_183, D_184)=k1_mcart_1(k1_mcart_1(D_184)) | ~m1_subset_1(D_184, k3_zfmisc_1(A_181, B_182, C_183)) | k1_xboole_0=C_183 | k1_xboole_0=B_182 | k1_xboole_0=A_181)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.55  tff(c_799, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_796])).
% 3.23/1.55  tff(c_802, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_708, c_799])).
% 3.23/1.55  tff(c_845, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_802])).
% 3.23/1.55  tff(c_853, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_60])).
% 3.23/1.55  tff(c_856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_853])).
% 3.23/1.55  tff(c_858, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_802])).
% 3.23/1.55  tff(c_722, plain, (![A_165, B_166, C_167, D_168]: (k6_mcart_1(A_165, B_166, C_167, D_168)=k2_mcart_1(k1_mcart_1(D_168)) | ~m1_subset_1(D_168, k3_zfmisc_1(A_165, B_166, C_167)) | k1_xboole_0=C_167 | k1_xboole_0=B_166 | k1_xboole_0=A_165)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.55  tff(c_725, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_722])).
% 3.23/1.55  tff(c_728, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_708, c_725])).
% 3.23/1.55  tff(c_907, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_858, c_728])).
% 3.23/1.55  tff(c_908, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_907])).
% 3.23/1.55  tff(c_917, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_60])).
% 3.23/1.55  tff(c_920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_917])).
% 3.23/1.55  tff(c_921, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_907])).
% 3.23/1.55  tff(c_634, plain, (![A_147, B_148, C_149]: (k2_zfmisc_1(k2_zfmisc_1(A_147, B_148), C_149)=k3_zfmisc_1(A_147, B_148, C_149))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_865, plain, (![A_192, A_193, B_194, C_195]: (r2_hidden(k1_mcart_1(A_192), k2_zfmisc_1(A_193, B_194)) | ~r2_hidden(A_192, k3_zfmisc_1(A_193, B_194, C_195)))), inference(superposition, [status(thm), theory('equality')], [c_634, c_16])).
% 3.23/1.55  tff(c_882, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_26, c_865])).
% 3.23/1.55  tff(c_896, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_882, c_14])).
% 3.23/1.55  tff(c_924, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_921, c_896])).
% 3.23/1.55  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_924])).
% 3.23/1.55  tff(c_927, plain, (![A_45]: (~r2_hidden(A_45, '#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 3.23/1.55  tff(c_447, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 3.23/1.55  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_927, c_447])).
% 3.23/1.55  tff(c_950, plain, (![A_45]: (~r2_hidden(A_45, '#skF_6'))), inference(splitRight, [status(thm)], [c_75])).
% 3.23/1.55  tff(c_1089, plain, (![B_223]: (v1_xboole_0(k2_zfmisc_1(B_223, '#skF_6')))), inference(resolution, [status(thm)], [c_1065, c_950])).
% 3.23/1.55  tff(c_1007, plain, (![B_211, C_212]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_211, C_212))), B_211) | v1_xboole_0(k2_zfmisc_1(B_211, C_212)))), inference(resolution, [status(thm)], [c_4, c_76])).
% 3.23/1.55  tff(c_1040, plain, (![B_214, C_215]: (~v1_xboole_0(B_214) | v1_xboole_0(k2_zfmisc_1(B_214, C_215)))), inference(resolution, [status(thm)], [c_1007, c_2])).
% 3.23/1.55  tff(c_1051, plain, (![A_220, B_221, C_222]: (~v1_xboole_0(k2_zfmisc_1(A_220, B_221)) | v1_xboole_0(k3_zfmisc_1(A_220, B_221, C_222)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1040])).
% 3.23/1.55  tff(c_1055, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1051, c_54])).
% 3.23/1.55  tff(c_1097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1055])).
% 3.23/1.55  tff(c_1098, plain, (![A_45]: (~r2_hidden(A_45, '#skF_7'))), inference(splitRight, [status(thm)], [c_73])).
% 3.23/1.55  tff(c_1106, plain, (![A_226, B_227, C_228]: (k2_zfmisc_1(k2_zfmisc_1(A_226, B_227), C_228)=k3_zfmisc_1(A_226, B_227, C_228))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_1127, plain, (![A_229, C_230, A_231, B_232]: (r2_hidden(k2_mcart_1(A_229), C_230) | ~r2_hidden(A_229, k3_zfmisc_1(A_231, B_232, C_230)))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_14])).
% 3.23/1.55  tff(c_1129, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_26, c_1127])).
% 3.23/1.55  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1098, c_1129])).
% 3.23/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.55  
% 3.23/1.55  Inference rules
% 3.23/1.55  ----------------------
% 3.23/1.55  #Ref     : 0
% 3.23/1.55  #Sup     : 232
% 3.23/1.55  #Fact    : 0
% 3.23/1.55  #Define  : 0
% 3.23/1.55  #Split   : 23
% 3.23/1.55  #Chain   : 0
% 3.23/1.55  #Close   : 0
% 3.23/1.55  
% 3.23/1.55  Ordering : KBO
% 3.23/1.55  
% 3.23/1.55  Simplification rules
% 3.23/1.55  ----------------------
% 3.23/1.55  #Subsume      : 20
% 3.23/1.55  #Demod        : 159
% 3.23/1.55  #Tautology    : 37
% 3.23/1.55  #SimpNegUnit  : 22
% 3.23/1.55  #BackRed      : 67
% 3.23/1.55  
% 3.23/1.55  #Partial instantiations: 0
% 3.23/1.55  #Strategies tried      : 1
% 3.23/1.55  
% 3.23/1.55  Timing (in seconds)
% 3.23/1.55  ----------------------
% 3.23/1.55  Preprocessing        : 0.31
% 3.23/1.55  Parsing              : 0.17
% 3.23/1.55  CNF conversion       : 0.02
% 3.23/1.55  Main loop            : 0.45
% 3.23/1.55  Inferencing          : 0.16
% 3.23/1.55  Reduction            : 0.14
% 3.23/1.55  Demodulation         : 0.10
% 3.23/1.55  BG Simplification    : 0.02
% 3.23/1.55  Subsumption          : 0.08
% 3.23/1.55  Abstraction          : 0.02
% 3.23/1.55  MUC search           : 0.00
% 3.23/1.55  Cooper               : 0.00
% 3.23/1.55  Total                : 0.81
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.55  Index Matching       : 0.00
% 3.23/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
