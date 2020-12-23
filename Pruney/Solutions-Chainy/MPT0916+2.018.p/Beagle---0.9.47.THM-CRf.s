%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:12 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 505 expanded)
%              Number of leaves         :   33 ( 177 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 (1399 expanded)
%              Number of equality atoms :   97 ( 447 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_28,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_424,plain,(
    ! [A_113,C_114,B_115] :
      ( r2_hidden(k2_mcart_1(A_113),C_114)
      | ~ r2_hidden(A_113,k2_zfmisc_1(B_115,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_432,plain,(
    ! [A_116,C_117,A_118,B_119] :
      ( r2_hidden(k2_mcart_1(A_116),C_117)
      | ~ r2_hidden(A_116,k3_zfmisc_1(A_118,B_119,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_424])).

tff(c_438,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_432])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_443,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_438,c_2])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_374,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,B_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_384,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_374])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_508,plain,(
    ! [B_133,C_134] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_133,C_134))),C_134)
      | v1_xboole_0(k2_zfmisc_1(B_133,C_134)) ) ),
    inference(resolution,[status(thm)],[c_4,c_424])).

tff(c_536,plain,(
    ! [C_139,B_140] :
      ( ~ v1_xboole_0(C_139)
      | v1_xboole_0(k2_zfmisc_1(B_140,C_139)) ) ),
    inference(resolution,[status(thm)],[c_508,c_2])).

tff(c_401,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden(k1_mcart_1(A_106),B_107)
      | ~ r2_hidden(A_106,k2_zfmisc_1(B_107,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_444,plain,(
    ! [B_120,C_121] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_120,C_121))),B_120)
      | v1_xboole_0(k2_zfmisc_1(B_120,C_121)) ) ),
    inference(resolution,[status(thm)],[c_4,c_401])).

tff(c_472,plain,(
    ! [B_126,C_127] :
      ( ~ v1_xboole_0(B_126)
      | v1_xboole_0(k2_zfmisc_1(B_126,C_127)) ) ),
    inference(resolution,[status(thm)],[c_444,c_2])).

tff(c_476,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_128,B_129))
      | v1_xboole_0(k3_zfmisc_1(A_128,B_129,C_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_472])).

tff(c_47,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_480,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_476,c_47])).

tff(c_543,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_536,c_480])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_385,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_374])).

tff(c_26,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_83,plain,(
    ! [A_49,B_50,C_51] : k2_zfmisc_1(k2_zfmisc_1(A_49,B_50),C_51) = k3_zfmisc_1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r2_hidden(k2_mcart_1(A_13),C_15)
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    ! [A_52,C_53,A_54,B_55] :
      ( r2_hidden(k2_mcart_1(A_52),C_53)
      | ~ r2_hidden(A_52,k3_zfmisc_1(A_54,B_55,C_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_16])).

tff(c_108,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_113,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_49,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_73,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden(k1_mcart_1(A_43),B_44)
      | ~ r2_hidden(A_43,k2_zfmisc_1(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    ! [B_56,C_57] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_56,C_57))),B_56)
      | v1_xboole_0(k2_zfmisc_1(B_56,C_57)) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_135,plain,(
    ! [B_56,C_57] :
      ( ~ v1_xboole_0(B_56)
      | v1_xboole_0(k2_zfmisc_1(B_56,C_57)) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_142,plain,(
    ! [B_62,C_63] :
      ( ~ v1_xboole_0(B_62)
      | v1_xboole_0(k2_zfmisc_1(B_62,C_63)) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_146,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_64,B_65))
      | v1_xboole_0(k3_zfmisc_1(A_64,B_65,C_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_150,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_146,c_47])).

tff(c_154,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_135,c_150])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_61,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_137,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k7_mcart_1(A_58,B_59,C_60,D_61) = k2_mcart_1(D_61)
      | ~ m1_subset_1(D_61,k3_zfmisc_1(A_58,B_59,C_60))
      | k1_xboole_0 = C_60
      | k1_xboole_0 = B_59
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_137])).

tff(c_155,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [B_40,A_41] :
      ( ~ r1_xboole_0(B_40,A_41)
      | ~ r1_tarski(B_40,A_41)
      | v1_xboole_0(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_168,plain,(
    ! [A_68] :
      ( ~ r1_tarski(A_68,'#skF_2')
      | v1_xboole_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_71])).

tff(c_171,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_61,c_168])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_171])).

tff(c_177,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_78,plain,(
    ! [A_46,C_47,B_48] :
      ( r2_hidden(k2_mcart_1(A_46),C_47)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [B_73,C_74] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_73,C_74))),C_74)
      | v1_xboole_0(k2_zfmisc_1(B_73,C_74)) ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_206,plain,(
    ! [C_75,B_76] :
      ( ~ v1_xboole_0(C_75)
      | v1_xboole_0(k2_zfmisc_1(B_76,C_75)) ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_213,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_206,c_150])).

tff(c_60,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_178,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k6_mcart_1(A_69,B_70,C_71,D_72) = k2_mcart_1(k1_mcart_1(D_72))
      | ~ m1_subset_1(D_72,k3_zfmisc_1(A_69,B_70,C_71))
      | k1_xboole_0 = C_71
      | k1_xboole_0 = B_70
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_178])).

tff(c_184,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_181])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_279,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,'#skF_3')
      | v1_xboole_0(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_71])).

tff(c_282,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_279])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_282])).

tff(c_288,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_313,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k5_mcart_1(A_94,B_95,C_96,D_97) = k1_mcart_1(k1_mcart_1(D_97))
      | ~ m1_subset_1(D_97,k3_zfmisc_1(A_94,B_95,C_96))
      | k1_xboole_0 = C_96
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_319,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_313])).

tff(c_322,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_288,c_319])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_359,plain,(
    ! [A_99] :
      ( ~ r1_tarski(A_99,'#skF_4')
      | v1_xboole_0(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_71])).

tff(c_362,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_59,c_359])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_362])).

tff(c_367,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k1_mcart_1(A_13),B_14)
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_294,plain,(
    ! [A_90,A_91,B_92,C_93] :
      ( r2_hidden(k1_mcart_1(A_90),k2_zfmisc_1(A_91,B_92))
      | ~ r2_hidden(A_90,k3_zfmisc_1(A_91,B_92,C_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_18])).

tff(c_311,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_294])).

tff(c_332,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_311,c_18])).

tff(c_369,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_332])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_369])).

tff(c_373,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_390,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_373,c_2])).

tff(c_386,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_374])).

tff(c_467,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k7_mcart_1(A_122,B_123,C_124,D_125) = k2_mcart_1(D_125)
      | ~ m1_subset_1(D_125,k3_zfmisc_1(A_122,B_123,C_124))
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_471,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_467])).

tff(c_485,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_396,plain,(
    ! [B_104,A_105] :
      ( ~ r1_xboole_0(B_104,A_105)
      | ~ r1_tarski(B_104,A_105)
      | v1_xboole_0(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_400,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_396])).

tff(c_498,plain,(
    ! [A_132] :
      ( ~ r1_tarski(A_132,'#skF_2')
      | v1_xboole_0(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_400])).

tff(c_501,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_386,c_498])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_501])).

tff(c_506,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_549,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_372,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_431,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_550,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_431])).

tff(c_553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_550])).

tff(c_554,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_556,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_554])).

tff(c_580,plain,(
    ! [A_149] :
      ( ~ r1_tarski(A_149,'#skF_3')
      | v1_xboole_0(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_400])).

tff(c_583,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_385,c_580])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_583])).

tff(c_588,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_606,plain,(
    ! [A_151] :
      ( ~ r1_tarski(A_151,'#skF_4')
      | v1_xboole_0(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_400])).

tff(c_609,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_384,c_606])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_609])).

tff(c_614,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_615,plain,(
    r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_619,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_615,c_2])).

tff(c_632,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k7_mcart_1(A_156,B_157,C_158,D_159) = k2_mcart_1(D_159)
      | ~ m1_subset_1(D_159,k3_zfmisc_1(A_156,B_157,C_158))
      | k1_xboole_0 = C_158
      | k1_xboole_0 = B_157
      | k1_xboole_0 = A_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_636,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_632])).

tff(c_712,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_726,plain,(
    ! [A_179] :
      ( ~ r1_tarski(A_179,'#skF_2')
      | v1_xboole_0(A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_400])).

tff(c_729,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_386,c_726])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_729])).

tff(c_735,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_673,plain,(
    ! [B_167,C_168] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_167,C_168))),C_168)
      | v1_xboole_0(k2_zfmisc_1(B_167,C_168)) ) ),
    inference(resolution,[status(thm)],[c_4,c_424])).

tff(c_699,plain,(
    ! [C_173,B_174] :
      ( ~ v1_xboole_0(C_173)
      | v1_xboole_0(k2_zfmisc_1(B_174,C_173)) ) ),
    inference(resolution,[status(thm)],[c_673,c_2])).

tff(c_637,plain,(
    ! [B_160,C_161] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_160,C_161))),B_160)
      | v1_xboole_0(k2_zfmisc_1(B_160,C_161)) ) ),
    inference(resolution,[status(thm)],[c_4,c_401])).

tff(c_660,plain,(
    ! [B_162,C_163] :
      ( ~ v1_xboole_0(B_162)
      | v1_xboole_0(k2_zfmisc_1(B_162,C_163)) ) ),
    inference(resolution,[status(thm)],[c_637,c_2])).

tff(c_664,plain,(
    ! [A_164,B_165,C_166] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_164,B_165))
      | v1_xboole_0(k3_zfmisc_1(A_164,B_165,C_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_660])).

tff(c_668,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_664,c_47])).

tff(c_706,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_699,c_668])).

tff(c_737,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k5_mcart_1(A_180,B_181,C_182,D_183) = k1_mcart_1(k1_mcart_1(D_183))
      | ~ m1_subset_1(D_183,k3_zfmisc_1(A_180,B_181,C_182))
      | k1_xboole_0 = C_182
      | k1_xboole_0 = B_181
      | k1_xboole_0 = A_180 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_740,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_737])).

tff(c_743,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_740])).

tff(c_750,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_767,plain,(
    ! [A_185] :
      ( ~ r1_tarski(A_185,'#skF_3')
      | v1_xboole_0(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_400])).

tff(c_770,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_385,c_767])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_770])).

tff(c_776,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_694,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k6_mcart_1(A_169,B_170,C_171,D_172) = k2_mcart_1(k1_mcart_1(D_172))
      | ~ m1_subset_1(D_172,k3_zfmisc_1(A_169,B_170,C_171))
      | k1_xboole_0 = C_171
      | k1_xboole_0 = B_170
      | k1_xboole_0 = A_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_698,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_694])).

tff(c_843,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_776,c_698])).

tff(c_844,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_861,plain,(
    ! [A_195] :
      ( ~ r1_tarski(A_195,'#skF_4')
      | v1_xboole_0(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_400])).

tff(c_864,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_384,c_861])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_864])).

tff(c_869,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_407,plain,(
    ! [A_110,B_111,C_112] : k2_zfmisc_1(k2_zfmisc_1(A_110,B_111),C_112) = k3_zfmisc_1(A_110,B_111,C_112) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_813,plain,(
    ! [A_190,A_191,B_192,C_193] :
      ( r2_hidden(k1_mcart_1(A_190),k2_zfmisc_1(A_191,B_192))
      | ~ r2_hidden(A_190,k3_zfmisc_1(A_191,B_192,C_193)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_18])).

tff(c_830,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_813])).

tff(c_839,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_830,c_16])).

tff(c_875,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_839])).

tff(c_877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.02  
% 3.79/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.79/2.02  
% 3.79/2.02  %Foreground sorts:
% 3.79/2.02  
% 3.79/2.02  
% 3.79/2.02  %Background operators:
% 3.79/2.02  
% 3.79/2.02  
% 3.79/2.02  %Foreground operators:
% 3.79/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/2.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.79/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/2.02  tff('#skF_7', type, '#skF_7': $i).
% 3.79/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/2.02  tff('#skF_5', type, '#skF_5': $i).
% 3.79/2.02  tff('#skF_6', type, '#skF_6': $i).
% 3.79/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.79/2.02  tff('#skF_2', type, '#skF_2': $i).
% 3.79/2.02  tff('#skF_3', type, '#skF_3': $i).
% 3.79/2.02  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.79/2.02  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.79/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/2.02  tff('#skF_8', type, '#skF_8': $i).
% 3.79/2.02  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.79/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/2.02  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.79/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.79/2.02  tff('#skF_4', type, '#skF_4': $i).
% 3.79/2.02  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.79/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/2.02  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.79/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/2.02  
% 3.79/2.06  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 3.79/2.06  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.79/2.06  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.79/2.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.79/2.06  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.79/2.06  tff(f_73, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.79/2.06  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.79/2.06  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.79/2.06  tff(c_28, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.06  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/2.06  tff(c_424, plain, (![A_113, C_114, B_115]: (r2_hidden(k2_mcart_1(A_113), C_114) | ~r2_hidden(A_113, k2_zfmisc_1(B_115, C_114)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/2.06  tff(c_432, plain, (![A_116, C_117, A_118, B_119]: (r2_hidden(k2_mcart_1(A_116), C_117) | ~r2_hidden(A_116, k3_zfmisc_1(A_118, B_119, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_424])).
% 3.79/2.06  tff(c_438, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_432])).
% 3.79/2.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/2.06  tff(c_443, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_438, c_2])).
% 3.79/2.06  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.06  tff(c_374, plain, (![A_100, B_101]: (r1_tarski(A_100, B_101) | ~m1_subset_1(A_100, k1_zfmisc_1(B_101)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.79/2.06  tff(c_384, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_374])).
% 3.79/2.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/2.06  tff(c_508, plain, (![B_133, C_134]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_133, C_134))), C_134) | v1_xboole_0(k2_zfmisc_1(B_133, C_134)))), inference(resolution, [status(thm)], [c_4, c_424])).
% 3.79/2.06  tff(c_536, plain, (![C_139, B_140]: (~v1_xboole_0(C_139) | v1_xboole_0(k2_zfmisc_1(B_140, C_139)))), inference(resolution, [status(thm)], [c_508, c_2])).
% 3.79/2.06  tff(c_401, plain, (![A_106, B_107, C_108]: (r2_hidden(k1_mcart_1(A_106), B_107) | ~r2_hidden(A_106, k2_zfmisc_1(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/2.06  tff(c_444, plain, (![B_120, C_121]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_120, C_121))), B_120) | v1_xboole_0(k2_zfmisc_1(B_120, C_121)))), inference(resolution, [status(thm)], [c_4, c_401])).
% 3.79/2.06  tff(c_472, plain, (![B_126, C_127]: (~v1_xboole_0(B_126) | v1_xboole_0(k2_zfmisc_1(B_126, C_127)))), inference(resolution, [status(thm)], [c_444, c_2])).
% 3.79/2.06  tff(c_476, plain, (![A_128, B_129, C_130]: (~v1_xboole_0(k2_zfmisc_1(A_128, B_129)) | v1_xboole_0(k3_zfmisc_1(A_128, B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_472])).
% 3.79/2.06  tff(c_47, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_2])).
% 3.79/2.06  tff(c_480, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_476, c_47])).
% 3.79/2.06  tff(c_543, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_536, c_480])).
% 3.79/2.06  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.06  tff(c_385, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_374])).
% 3.79/2.06  tff(c_26, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.06  tff(c_48, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_26])).
% 3.79/2.06  tff(c_83, plain, (![A_49, B_50, C_51]: (k2_zfmisc_1(k2_zfmisc_1(A_49, B_50), C_51)=k3_zfmisc_1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/2.06  tff(c_16, plain, (![A_13, C_15, B_14]: (r2_hidden(k2_mcart_1(A_13), C_15) | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/2.06  tff(c_102, plain, (![A_52, C_53, A_54, B_55]: (r2_hidden(k2_mcart_1(A_52), C_53) | ~r2_hidden(A_52, k3_zfmisc_1(A_54, B_55, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_16])).
% 3.79/2.06  tff(c_108, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_102])).
% 3.79/2.06  tff(c_113, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_108, c_2])).
% 3.79/2.06  tff(c_49, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.79/2.06  tff(c_59, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_49])).
% 3.79/2.06  tff(c_73, plain, (![A_43, B_44, C_45]: (r2_hidden(k1_mcart_1(A_43), B_44) | ~r2_hidden(A_43, k2_zfmisc_1(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/2.06  tff(c_114, plain, (![B_56, C_57]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_56, C_57))), B_56) | v1_xboole_0(k2_zfmisc_1(B_56, C_57)))), inference(resolution, [status(thm)], [c_4, c_73])).
% 3.79/2.06  tff(c_135, plain, (![B_56, C_57]: (~v1_xboole_0(B_56) | v1_xboole_0(k2_zfmisc_1(B_56, C_57)))), inference(resolution, [status(thm)], [c_114, c_2])).
% 3.79/2.06  tff(c_142, plain, (![B_62, C_63]: (~v1_xboole_0(B_62) | v1_xboole_0(k2_zfmisc_1(B_62, C_63)))), inference(resolution, [status(thm)], [c_114, c_2])).
% 3.79/2.06  tff(c_146, plain, (![A_64, B_65, C_66]: (~v1_xboole_0(k2_zfmisc_1(A_64, B_65)) | v1_xboole_0(k3_zfmisc_1(A_64, B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_142])).
% 3.79/2.06  tff(c_150, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_146, c_47])).
% 3.79/2.06  tff(c_154, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_135, c_150])).
% 3.79/2.06  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.06  tff(c_61, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_49])).
% 3.79/2.06  tff(c_30, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.06  tff(c_137, plain, (![A_58, B_59, C_60, D_61]: (k7_mcart_1(A_58, B_59, C_60, D_61)=k2_mcart_1(D_61) | ~m1_subset_1(D_61, k3_zfmisc_1(A_58, B_59, C_60)) | k1_xboole_0=C_60 | k1_xboole_0=B_59 | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_141, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_137])).
% 3.79/2.06  tff(c_155, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_141])).
% 3.79/2.06  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.79/2.06  tff(c_67, plain, (![B_40, A_41]: (~r1_xboole_0(B_40, A_41) | ~r1_tarski(B_40, A_41) | v1_xboole_0(B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.79/2.06  tff(c_71, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_6, c_67])).
% 3.79/2.06  tff(c_168, plain, (![A_68]: (~r1_tarski(A_68, '#skF_2') | v1_xboole_0(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_71])).
% 3.79/2.06  tff(c_171, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_61, c_168])).
% 3.79/2.06  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_171])).
% 3.79/2.06  tff(c_177, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_141])).
% 3.79/2.06  tff(c_78, plain, (![A_46, C_47, B_48]: (r2_hidden(k2_mcart_1(A_46), C_47) | ~r2_hidden(A_46, k2_zfmisc_1(B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/2.06  tff(c_185, plain, (![B_73, C_74]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_73, C_74))), C_74) | v1_xboole_0(k2_zfmisc_1(B_73, C_74)))), inference(resolution, [status(thm)], [c_4, c_78])).
% 3.79/2.06  tff(c_206, plain, (![C_75, B_76]: (~v1_xboole_0(C_75) | v1_xboole_0(k2_zfmisc_1(B_76, C_75)))), inference(resolution, [status(thm)], [c_185, c_2])).
% 3.79/2.06  tff(c_213, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_206, c_150])).
% 3.79/2.06  tff(c_60, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_49])).
% 3.79/2.06  tff(c_178, plain, (![A_69, B_70, C_71, D_72]: (k6_mcart_1(A_69, B_70, C_71, D_72)=k2_mcart_1(k1_mcart_1(D_72)) | ~m1_subset_1(D_72, k3_zfmisc_1(A_69, B_70, C_71)) | k1_xboole_0=C_71 | k1_xboole_0=B_70 | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_181, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_178])).
% 3.79/2.06  tff(c_184, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_177, c_181])).
% 3.79/2.06  tff(c_252, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_184])).
% 3.79/2.06  tff(c_279, plain, (![A_89]: (~r1_tarski(A_89, '#skF_3') | v1_xboole_0(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_71])).
% 3.79/2.06  tff(c_282, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_279])).
% 3.79/2.06  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_282])).
% 3.79/2.06  tff(c_288, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_184])).
% 3.79/2.06  tff(c_313, plain, (![A_94, B_95, C_96, D_97]: (k5_mcart_1(A_94, B_95, C_96, D_97)=k1_mcart_1(k1_mcart_1(D_97)) | ~m1_subset_1(D_97, k3_zfmisc_1(A_94, B_95, C_96)) | k1_xboole_0=C_96 | k1_xboole_0=B_95 | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_319, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_313])).
% 3.79/2.06  tff(c_322, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_177, c_288, c_319])).
% 3.79/2.06  tff(c_342, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_322])).
% 3.79/2.06  tff(c_359, plain, (![A_99]: (~r1_tarski(A_99, '#skF_4') | v1_xboole_0(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_71])).
% 3.79/2.06  tff(c_362, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_59, c_359])).
% 3.79/2.06  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_362])).
% 3.79/2.06  tff(c_367, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_322])).
% 3.79/2.06  tff(c_18, plain, (![A_13, B_14, C_15]: (r2_hidden(k1_mcart_1(A_13), B_14) | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/2.06  tff(c_294, plain, (![A_90, A_91, B_92, C_93]: (r2_hidden(k1_mcart_1(A_90), k2_zfmisc_1(A_91, B_92)) | ~r2_hidden(A_90, k3_zfmisc_1(A_91, B_92, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_18])).
% 3.79/2.06  tff(c_311, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_294])).
% 3.79/2.06  tff(c_332, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_311, c_18])).
% 3.79/2.06  tff(c_369, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_332])).
% 3.79/2.06  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_369])).
% 3.79/2.06  tff(c_373, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 3.79/2.06  tff(c_390, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_373, c_2])).
% 3.79/2.06  tff(c_386, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_374])).
% 3.79/2.06  tff(c_467, plain, (![A_122, B_123, C_124, D_125]: (k7_mcart_1(A_122, B_123, C_124, D_125)=k2_mcart_1(D_125) | ~m1_subset_1(D_125, k3_zfmisc_1(A_122, B_123, C_124)) | k1_xboole_0=C_124 | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_471, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_467])).
% 3.79/2.06  tff(c_485, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_471])).
% 3.79/2.06  tff(c_396, plain, (![B_104, A_105]: (~r1_xboole_0(B_104, A_105) | ~r1_tarski(B_104, A_105) | v1_xboole_0(B_104))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.79/2.06  tff(c_400, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_6, c_396])).
% 3.79/2.06  tff(c_498, plain, (![A_132]: (~r1_tarski(A_132, '#skF_2') | v1_xboole_0(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_400])).
% 3.79/2.06  tff(c_501, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_386, c_498])).
% 3.79/2.06  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_501])).
% 3.79/2.06  tff(c_506, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_471])).
% 3.79/2.06  tff(c_549, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_506])).
% 3.79/2.06  tff(c_372, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_26])).
% 3.79/2.06  tff(c_431, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_372])).
% 3.79/2.06  tff(c_550, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_549, c_431])).
% 3.79/2.06  tff(c_553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_438, c_550])).
% 3.79/2.06  tff(c_554, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_506])).
% 3.79/2.06  tff(c_556, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_554])).
% 3.79/2.06  tff(c_580, plain, (![A_149]: (~r1_tarski(A_149, '#skF_3') | v1_xboole_0(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_400])).
% 3.79/2.06  tff(c_583, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_385, c_580])).
% 3.79/2.06  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_583])).
% 3.79/2.06  tff(c_588, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_554])).
% 3.79/2.06  tff(c_606, plain, (![A_151]: (~r1_tarski(A_151, '#skF_4') | v1_xboole_0(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_400])).
% 3.79/2.06  tff(c_609, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_384, c_606])).
% 3.79/2.06  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_443, c_609])).
% 3.79/2.06  tff(c_614, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_372])).
% 3.79/2.06  tff(c_615, plain, (r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_372])).
% 3.79/2.06  tff(c_619, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_615, c_2])).
% 3.79/2.06  tff(c_632, plain, (![A_156, B_157, C_158, D_159]: (k7_mcart_1(A_156, B_157, C_158, D_159)=k2_mcart_1(D_159) | ~m1_subset_1(D_159, k3_zfmisc_1(A_156, B_157, C_158)) | k1_xboole_0=C_158 | k1_xboole_0=B_157 | k1_xboole_0=A_156)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_636, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_632])).
% 3.79/2.06  tff(c_712, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_636])).
% 3.79/2.06  tff(c_726, plain, (![A_179]: (~r1_tarski(A_179, '#skF_2') | v1_xboole_0(A_179))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_400])).
% 3.79/2.06  tff(c_729, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_386, c_726])).
% 3.79/2.06  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_729])).
% 3.79/2.06  tff(c_735, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_636])).
% 3.79/2.06  tff(c_673, plain, (![B_167, C_168]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_167, C_168))), C_168) | v1_xboole_0(k2_zfmisc_1(B_167, C_168)))), inference(resolution, [status(thm)], [c_4, c_424])).
% 3.79/2.06  tff(c_699, plain, (![C_173, B_174]: (~v1_xboole_0(C_173) | v1_xboole_0(k2_zfmisc_1(B_174, C_173)))), inference(resolution, [status(thm)], [c_673, c_2])).
% 3.79/2.06  tff(c_637, plain, (![B_160, C_161]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_160, C_161))), B_160) | v1_xboole_0(k2_zfmisc_1(B_160, C_161)))), inference(resolution, [status(thm)], [c_4, c_401])).
% 3.79/2.06  tff(c_660, plain, (![B_162, C_163]: (~v1_xboole_0(B_162) | v1_xboole_0(k2_zfmisc_1(B_162, C_163)))), inference(resolution, [status(thm)], [c_637, c_2])).
% 3.79/2.06  tff(c_664, plain, (![A_164, B_165, C_166]: (~v1_xboole_0(k2_zfmisc_1(A_164, B_165)) | v1_xboole_0(k3_zfmisc_1(A_164, B_165, C_166)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_660])).
% 3.79/2.06  tff(c_668, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_664, c_47])).
% 3.79/2.06  tff(c_706, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_699, c_668])).
% 3.79/2.06  tff(c_737, plain, (![A_180, B_181, C_182, D_183]: (k5_mcart_1(A_180, B_181, C_182, D_183)=k1_mcart_1(k1_mcart_1(D_183)) | ~m1_subset_1(D_183, k3_zfmisc_1(A_180, B_181, C_182)) | k1_xboole_0=C_182 | k1_xboole_0=B_181 | k1_xboole_0=A_180)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_740, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_737])).
% 3.79/2.06  tff(c_743, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_735, c_740])).
% 3.79/2.06  tff(c_750, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_743])).
% 3.79/2.06  tff(c_767, plain, (![A_185]: (~r1_tarski(A_185, '#skF_3') | v1_xboole_0(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_400])).
% 3.79/2.06  tff(c_770, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_385, c_767])).
% 3.79/2.06  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_706, c_770])).
% 3.79/2.06  tff(c_776, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_743])).
% 3.79/2.06  tff(c_694, plain, (![A_169, B_170, C_171, D_172]: (k6_mcart_1(A_169, B_170, C_171, D_172)=k2_mcart_1(k1_mcart_1(D_172)) | ~m1_subset_1(D_172, k3_zfmisc_1(A_169, B_170, C_171)) | k1_xboole_0=C_171 | k1_xboole_0=B_170 | k1_xboole_0=A_169)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.06  tff(c_698, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_694])).
% 3.79/2.06  tff(c_843, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_735, c_776, c_698])).
% 3.79/2.06  tff(c_844, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_843])).
% 3.79/2.06  tff(c_861, plain, (![A_195]: (~r1_tarski(A_195, '#skF_4') | v1_xboole_0(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_844, c_400])).
% 3.79/2.06  tff(c_864, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_384, c_861])).
% 3.79/2.06  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_619, c_864])).
% 3.79/2.06  tff(c_869, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_843])).
% 3.79/2.06  tff(c_407, plain, (![A_110, B_111, C_112]: (k2_zfmisc_1(k2_zfmisc_1(A_110, B_111), C_112)=k3_zfmisc_1(A_110, B_111, C_112))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/2.06  tff(c_813, plain, (![A_190, A_191, B_192, C_193]: (r2_hidden(k1_mcart_1(A_190), k2_zfmisc_1(A_191, B_192)) | ~r2_hidden(A_190, k3_zfmisc_1(A_191, B_192, C_193)))), inference(superposition, [status(thm), theory('equality')], [c_407, c_18])).
% 3.79/2.06  tff(c_830, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_813])).
% 3.79/2.06  tff(c_839, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_830, c_16])).
% 3.79/2.06  tff(c_875, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_869, c_839])).
% 3.79/2.06  tff(c_877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_614, c_875])).
% 3.79/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.06  
% 3.79/2.06  Inference rules
% 3.79/2.06  ----------------------
% 3.79/2.06  #Ref     : 0
% 3.79/2.06  #Sup     : 179
% 3.79/2.06  #Fact    : 0
% 3.79/2.06  #Define  : 0
% 3.79/2.06  #Split   : 15
% 3.79/2.06  #Chain   : 0
% 3.79/2.06  #Close   : 0
% 3.79/2.06  
% 3.79/2.06  Ordering : KBO
% 3.79/2.06  
% 3.79/2.06  Simplification rules
% 3.79/2.06  ----------------------
% 3.79/2.06  #Subsume      : 19
% 3.79/2.06  #Demod        : 132
% 3.79/2.06  #Tautology    : 45
% 3.79/2.06  #SimpNegUnit  : 18
% 3.79/2.06  #BackRed      : 51
% 3.79/2.06  
% 3.79/2.06  #Partial instantiations: 0
% 3.79/2.06  #Strategies tried      : 1
% 3.79/2.06  
% 3.79/2.06  Timing (in seconds)
% 3.79/2.06  ----------------------
% 3.79/2.07  Preprocessing        : 0.50
% 3.79/2.07  Parsing              : 0.26
% 3.79/2.07  CNF conversion       : 0.04
% 3.79/2.07  Main loop            : 0.64
% 3.79/2.07  Inferencing          : 0.24
% 3.79/2.07  Reduction            : 0.20
% 3.79/2.07  Demodulation         : 0.13
% 3.79/2.07  BG Simplification    : 0.03
% 3.79/2.07  Subsumption          : 0.10
% 3.79/2.07  Abstraction          : 0.04
% 3.79/2.07  MUC search           : 0.00
% 3.79/2.07  Cooper               : 0.00
% 3.79/2.07  Total                : 1.24
% 3.79/2.07  Index Insertion      : 0.00
% 3.79/2.07  Index Deletion       : 0.00
% 3.79/2.07  Index Matching       : 0.00
% 3.79/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
