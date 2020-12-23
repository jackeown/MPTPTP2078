%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 9.23s
% Output     : CNFRefutation 9.57s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 584 expanded)
%              Number of leaves         :   31 ( 198 expanded)
%              Depth                    :   12
%              Number of atoms          :  231 (1235 expanded)
%              Number of equality atoms :   41 ( 218 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_20089,plain,(
    ! [A_3052,B_3053,C_3054] :
      ( r2_hidden('#skF_5'(A_3052,B_3053,C_3054),B_3053)
      | r2_hidden('#skF_6'(A_3052,B_3053,C_3054),C_3054)
      | k2_zfmisc_1(A_3052,B_3053) = C_3054 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10398,plain,(
    ! [A_2428,B_2429,C_2430] :
      ( r2_hidden('#skF_5'(A_2428,B_2429,C_2430),B_2429)
      | r2_hidden('#skF_6'(A_2428,B_2429,C_2430),C_2430)
      | k2_zfmisc_1(A_2428,B_2429) = C_2430 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9600,plain,(
    ! [A_2360,B_2361,C_2362,D_2363] :
      ( r2_hidden(k4_tarski(A_2360,B_2361),k2_zfmisc_1(C_2362,D_2363))
      | ~ r2_hidden(B_2361,D_2363)
      | ~ r2_hidden(A_2360,C_2362) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_118,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_10','#skF_12')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_135,plain,(
    ! [A_72] : r1_tarski(A_72,A_72) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_139,plain,(
    ! [A_72] : k3_xboole_0(A_72,A_72) = A_72 ),
    inference(resolution,[status(thm)],[c_135,c_12])).

tff(c_199,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_2'(A_84,B_85),k3_xboole_0(A_84,B_85))
      | r1_xboole_0(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_210,plain,(
    ! [A_72] :
      ( r2_hidden('#skF_2'(A_72,A_72),A_72)
      | r1_xboole_0(A_72,A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_199])).

tff(c_58,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_393,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( r2_hidden(k4_tarski(A_108,B_109),k2_zfmisc_1(C_110,D_111))
      | ~ r2_hidden(B_109,D_111)
      | ~ r2_hidden(A_108,C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8308,plain,(
    ! [C_402,D_404,B_403,A_401,B_405] :
      ( r2_hidden(k4_tarski(A_401,B_405),B_403)
      | ~ r1_tarski(k2_zfmisc_1(C_402,D_404),B_403)
      | ~ r2_hidden(B_405,D_404)
      | ~ r2_hidden(A_401,C_402) ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_8923,plain,(
    ! [A_410,B_411] :
      ( r2_hidden(k4_tarski(A_410,B_411),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_411,'#skF_10')
      | ~ r2_hidden(A_410,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_58,c_8308])).

tff(c_46,plain,(
    ! [A_49,C_51,B_50,D_52] :
      ( r2_hidden(A_49,C_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8950,plain,(
    ! [A_410,B_411] :
      ( r2_hidden(A_410,'#skF_11')
      | ~ r2_hidden(B_411,'#skF_10')
      | ~ r2_hidden(A_410,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_8923,c_46])).

tff(c_8954,plain,(
    ! [B_412] : ~ r2_hidden(B_412,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_8950])).

tff(c_9022,plain,(
    r1_xboole_0('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_210,c_8954])).

tff(c_963,plain,(
    ! [A_168,B_169,C_170] :
      ( r2_hidden('#skF_5'(A_168,B_169,C_170),B_169)
      | r2_hidden('#skF_6'(A_168,B_169,C_170),C_170)
      | k2_zfmisc_1(A_168,B_169) = C_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [A_13] : k3_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_100,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [A_13,C_64] :
      ( ~ r1_xboole_0(k1_xboole_0,A_13)
      | ~ r2_hidden(C_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_100])).

tff(c_104,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_1155,plain,(
    ! [A_185,B_186] :
      ( r2_hidden('#skF_5'(A_185,B_186,k1_xboole_0),B_186)
      | k2_zfmisc_1(A_185,B_186) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_963,c_104])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1225,plain,(
    ! [A_189,B_190,A_191] :
      ( ~ r1_xboole_0(A_189,B_190)
      | k2_zfmisc_1(A_191,k3_xboole_0(A_189,B_190)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1155,c_10])).

tff(c_48,plain,(
    ! [B_54,A_53] :
      ( k1_xboole_0 = B_54
      | k1_xboole_0 = A_53
      | k2_zfmisc_1(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1298,plain,(
    ! [A_189,B_190,A_191] :
      ( k3_xboole_0(A_189,B_190) = k1_xboole_0
      | k1_xboole_0 = A_191
      | ~ r1_xboole_0(A_189,B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_48])).

tff(c_1359,plain,(
    ! [A_189,B_190] :
      ( k3_xboole_0(A_189,B_190) = k1_xboole_0
      | ~ r1_xboole_0(A_189,B_190) ) ),
    inference(splitLeft,[status(thm)],[c_1298])).

tff(c_9044,plain,(
    k3_xboole_0('#skF_10','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9022,c_1359])).

tff(c_9073,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_9044])).

tff(c_99,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_12])).

tff(c_170,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(C_10,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_291,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_207,plain,
    ( r2_hidden('#skF_2'(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_9','#skF_10'))
    | r1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_199])).

tff(c_633,plain,(
    r2_hidden('#skF_2'(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_207])).

tff(c_761,plain,(
    ! [A_152,B_153,D_154] :
      ( r2_hidden('#skF_8'(A_152,B_153,k2_zfmisc_1(A_152,B_153),D_154),B_153)
      | ~ r2_hidden(D_154,k2_zfmisc_1(A_152,B_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_235,plain,(
    ! [A_91] :
      ( r2_hidden('#skF_2'(A_91,A_91),A_91)
      | r1_xboole_0(A_91,A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_199])).

tff(c_449,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_2'(A_119,A_119),B_120)
      | ~ r1_tarski(A_119,B_120)
      | r1_xboole_0(A_119,A_119) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_463,plain,(
    ! [A_121] :
      ( ~ r1_tarski(A_121,k1_xboole_0)
      | r1_xboole_0(A_121,A_121) ) ),
    inference(resolution,[status(thm)],[c_449,c_104])).

tff(c_140,plain,(
    ! [A_73] : k3_xboole_0(A_73,A_73) = A_73 ),
    inference(resolution,[status(thm)],[c_135,c_12])).

tff(c_146,plain,(
    ! [A_73,C_10] :
      ( ~ r1_xboole_0(A_73,A_73)
      | ~ r2_hidden(C_10,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_475,plain,(
    ! [C_10,A_121] :
      ( ~ r2_hidden(C_10,A_121)
      | ~ r1_tarski(A_121,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_463,c_146])).

tff(c_799,plain,(
    ! [B_155,D_156,A_157] :
      ( ~ r1_tarski(B_155,k1_xboole_0)
      | ~ r2_hidden(D_156,k2_zfmisc_1(A_157,B_155)) ) ),
    inference(resolution,[status(thm)],[c_761,c_475])).

tff(c_837,plain,(
    ~ r1_tarski('#skF_10',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_633,c_799])).

tff(c_9141,plain,(
    ~ r1_tarski('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9073,c_837])).

tff(c_9165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_9141])).

tff(c_9167,plain,(
    ! [A_413] :
      ( r2_hidden(A_413,'#skF_11')
      | ~ r2_hidden(A_413,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_8950])).

tff(c_9328,plain,(
    ! [A_420] :
      ( r1_tarski(A_420,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_420,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_9167,c_4])).

tff(c_9336,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_9328])).

tff(c_9341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_83,c_9336])).

tff(c_9343,plain,(
    ! [A_421] : k1_xboole_0 = A_421 ),
    inference(splitRight,[status(thm)],[c_1298])).

tff(c_195,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_98,B_99,B_100] :
      ( r2_hidden('#skF_1'(A_98,B_99),B_100)
      | ~ r1_tarski(A_98,B_100)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_413,plain,(
    ! [A_112,B_113,A_114,B_115] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r1_tarski(A_114,k3_xboole_0(A_112,B_113))
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_292,c_10])).

tff(c_422,plain,(
    ! [A_72,A_114,B_115] :
      ( ~ r1_xboole_0(A_72,A_72)
      | ~ r1_tarski(A_114,A_72)
      | r1_tarski(A_114,B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_413])).

tff(c_645,plain,(
    ! [A_137,A_138,B_139] :
      ( ~ r1_tarski(A_137,A_138)
      | r1_tarski(A_137,B_139)
      | ~ r1_tarski(A_138,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_463,c_422])).

tff(c_659,plain,(
    ! [B_139] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),B_139)
      | ~ r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_58,c_645])).

tff(c_884,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_9377,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9343,c_884])).

tff(c_9530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_9377])).

tff(c_9531,plain,(
    ! [B_139] : r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),B_139) ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_476,plain,(
    ! [C_122,A_123] :
      ( ~ r2_hidden(C_122,A_123)
      | ~ r1_tarski(A_123,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_463,c_146])).

tff(c_516,plain,(
    ! [A_126,B_127] :
      ( ~ r1_tarski(k3_xboole_0(A_126,B_127),k1_xboole_0)
      | r1_xboole_0(A_126,B_127) ) ),
    inference(resolution,[status(thm)],[c_8,c_476])).

tff(c_526,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k1_xboole_0)
    | r1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_516])).

tff(c_534,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_526])).

tff(c_9536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9531,c_534])).

tff(c_9537,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_9619,plain,(
    ! [B_2361,A_2360] :
      ( ~ r2_hidden(B_2361,'#skF_10')
      | ~ r2_hidden(A_2360,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_9600,c_9537])).

tff(c_9638,plain,(
    ! [A_2365] : ~ r2_hidden(A_2365,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_9619])).

tff(c_9648,plain,(
    ! [B_2] : r1_tarski('#skF_9',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_9638])).

tff(c_9659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9648,c_83])).

tff(c_9660,plain,(
    ! [B_2361] : ~ r2_hidden(B_2361,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_9619])).

tff(c_11315,plain,(
    ! [A_2511,B_2512] :
      ( r2_hidden('#skF_5'(A_2511,B_2512,'#skF_10'),B_2512)
      | k2_zfmisc_1(A_2511,B_2512) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_10398,c_9660])).

tff(c_11400,plain,(
    ! [A_2511] : k2_zfmisc_1(A_2511,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_11315,c_9660])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_11421,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11400,c_56])).

tff(c_11432,plain,(
    ! [A_2513] : k2_zfmisc_1(A_2513,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_11315,c_9660])).

tff(c_52,plain,(
    ! [B_54] : k2_zfmisc_1(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11540,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_11432,c_52])).

tff(c_11573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11421,c_11540])).

tff(c_11575,plain,(
    ! [A_2514] : ~ r1_xboole_0(k1_xboole_0,A_2514) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_11580,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_11575])).

tff(c_11581,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11948,plain,(
    ! [A_2567,B_2568,C_2569,D_2570] :
      ( r2_hidden(k4_tarski(A_2567,B_2568),k2_zfmisc_1(C_2569,D_2570))
      | ~ r2_hidden(B_2568,D_2570)
      | ~ r2_hidden(A_2567,C_2569) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16934,plain,(
    ! [B_2836,B_2835,A_2838,D_2834,C_2837] :
      ( r2_hidden(k4_tarski(A_2838,B_2835),B_2836)
      | ~ r1_tarski(k2_zfmisc_1(C_2837,D_2834),B_2836)
      | ~ r2_hidden(B_2835,D_2834)
      | ~ r2_hidden(A_2838,C_2837) ) ),
    inference(resolution,[status(thm)],[c_11948,c_2])).

tff(c_17066,plain,(
    ! [A_2844,B_2845] :
      ( r2_hidden(k4_tarski(A_2844,B_2845),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_2845,'#skF_10')
      | ~ r2_hidden(A_2844,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_58,c_16934])).

tff(c_44,plain,(
    ! [B_50,D_52,A_49,C_51] :
      ( r2_hidden(B_50,D_52)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_17094,plain,(
    ! [B_2845,A_2844] :
      ( r2_hidden(B_2845,'#skF_12')
      | ~ r2_hidden(B_2845,'#skF_10')
      | ~ r2_hidden(A_2844,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_17066,c_44])).

tff(c_17528,plain,(
    ! [A_2844] : ~ r2_hidden(A_2844,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_17094])).

tff(c_11582,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11583,plain,(
    ! [A_2515,B_2516] :
      ( k3_xboole_0(A_2515,B_2516) = A_2515
      | ~ r1_tarski(A_2515,B_2516) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11594,plain,(
    k3_xboole_0('#skF_9','#skF_11') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_11582,c_11583])).

tff(c_11612,plain,(
    ! [A_2520,B_2521,C_2522] :
      ( ~ r1_xboole_0(A_2520,B_2521)
      | ~ r2_hidden(C_2522,k3_xboole_0(A_2520,B_2521)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11621,plain,(
    ! [C_2522] :
      ( ~ r1_xboole_0('#skF_9','#skF_11')
      | ~ r2_hidden(C_2522,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11594,c_11612])).

tff(c_11635,plain,(
    ~ r1_xboole_0('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_11621])).

tff(c_11722,plain,(
    ! [A_2544,B_2545] :
      ( r2_hidden('#skF_2'(A_2544,B_2545),k3_xboole_0(A_2544,B_2545))
      | r1_xboole_0(A_2544,B_2545) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11739,plain,
    ( r2_hidden('#skF_2'('#skF_9','#skF_11'),'#skF_9')
    | r1_xboole_0('#skF_9','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_11594,c_11722])).

tff(c_11744,plain,(
    r2_hidden('#skF_2'('#skF_9','#skF_11'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_11635,c_11739])).

tff(c_17530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17528,c_11744])).

tff(c_17532,plain,(
    ! [B_2855] :
      ( r2_hidden(B_2855,'#skF_12')
      | ~ r2_hidden(B_2855,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_17094])).

tff(c_17951,plain,(
    ! [B_2863] :
      ( r2_hidden('#skF_1'('#skF_10',B_2863),'#skF_12')
      | r1_tarski('#skF_10',B_2863) ) ),
    inference(resolution,[status(thm)],[c_6,c_17532])).

tff(c_17960,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_17951,c_4])).

tff(c_17966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11581,c_11581,c_17960])).

tff(c_17967,plain,(
    ! [C_2522] : ~ r2_hidden(C_2522,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_11621])).

tff(c_20770,plain,(
    ! [A_3087,B_3088] :
      ( r2_hidden('#skF_5'(A_3087,B_3088,'#skF_9'),B_3088)
      | k2_zfmisc_1(A_3087,B_3088) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_20089,c_17967])).

tff(c_20853,plain,(
    ! [A_3089] : k2_zfmisc_1(A_3089,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_20770,c_17967])).

tff(c_20933,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_20853,c_52])).

tff(c_20962,plain,(
    ! [B_54] : k2_zfmisc_1('#skF_9',B_54) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20933,c_20933,c_52])).

tff(c_20964,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20933,c_56])).

tff(c_21088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20962,c_20964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.23/3.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.23/3.16  
% 9.23/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.23/3.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 9.23/3.17  
% 9.23/3.17  %Foreground sorts:
% 9.23/3.17  
% 9.23/3.17  
% 9.23/3.17  %Background operators:
% 9.23/3.17  
% 9.23/3.17  
% 9.23/3.17  %Foreground operators:
% 9.23/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.23/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.23/3.17  tff('#skF_11', type, '#skF_11': $i).
% 9.23/3.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.23/3.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.23/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.23/3.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.23/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.23/3.17  tff('#skF_10', type, '#skF_10': $i).
% 9.23/3.17  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 9.23/3.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.23/3.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.23/3.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 9.23/3.17  tff('#skF_9', type, '#skF_9': $i).
% 9.23/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.23/3.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.23/3.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.23/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.23/3.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.23/3.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.23/3.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.23/3.17  tff('#skF_12', type, '#skF_12': $i).
% 9.23/3.17  
% 9.57/3.19  tff(f_66, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 9.57/3.19  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.57/3.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.57/3.19  tff(f_72, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 9.57/3.19  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 9.57/3.19  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.57/3.19  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.57/3.19  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.57/3.19  tff(f_78, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.57/3.19  tff(c_20089, plain, (![A_3052, B_3053, C_3054]: (r2_hidden('#skF_5'(A_3052, B_3053, C_3054), B_3053) | r2_hidden('#skF_6'(A_3052, B_3053, C_3054), C_3054) | k2_zfmisc_1(A_3052, B_3053)=C_3054)), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.57/3.19  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.57/3.19  tff(c_10398, plain, (![A_2428, B_2429, C_2430]: (r2_hidden('#skF_5'(A_2428, B_2429, C_2430), B_2429) | r2_hidden('#skF_6'(A_2428, B_2429, C_2430), C_2430) | k2_zfmisc_1(A_2428, B_2429)=C_2430)), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.57/3.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.57/3.19  tff(c_9600, plain, (![A_2360, B_2361, C_2362, D_2363]: (r2_hidden(k4_tarski(A_2360, B_2361), k2_zfmisc_1(C_2362, D_2363)) | ~r2_hidden(B_2361, D_2363) | ~r2_hidden(A_2360, C_2362))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.57/3.19  tff(c_118, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.57/3.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.57/3.19  tff(c_131, plain, (![A_70]: (r1_tarski(A_70, A_70))), inference(resolution, [status(thm)], [c_118, c_4])).
% 9.57/3.19  tff(c_54, plain, (~r1_tarski('#skF_10', '#skF_12') | ~r1_tarski('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.57/3.19  tff(c_83, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_54])).
% 9.57/3.19  tff(c_135, plain, (![A_72]: (r1_tarski(A_72, A_72))), inference(resolution, [status(thm)], [c_118, c_4])).
% 9.57/3.19  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.57/3.19  tff(c_139, plain, (![A_72]: (k3_xboole_0(A_72, A_72)=A_72)), inference(resolution, [status(thm)], [c_135, c_12])).
% 9.57/3.19  tff(c_199, plain, (![A_84, B_85]: (r2_hidden('#skF_2'(A_84, B_85), k3_xboole_0(A_84, B_85)) | r1_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.57/3.19  tff(c_210, plain, (![A_72]: (r2_hidden('#skF_2'(A_72, A_72), A_72) | r1_xboole_0(A_72, A_72))), inference(superposition, [status(thm), theory('equality')], [c_139, c_199])).
% 9.57/3.19  tff(c_58, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.57/3.19  tff(c_393, plain, (![A_108, B_109, C_110, D_111]: (r2_hidden(k4_tarski(A_108, B_109), k2_zfmisc_1(C_110, D_111)) | ~r2_hidden(B_109, D_111) | ~r2_hidden(A_108, C_110))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.57/3.19  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.57/3.19  tff(c_8308, plain, (![C_402, D_404, B_403, A_401, B_405]: (r2_hidden(k4_tarski(A_401, B_405), B_403) | ~r1_tarski(k2_zfmisc_1(C_402, D_404), B_403) | ~r2_hidden(B_405, D_404) | ~r2_hidden(A_401, C_402))), inference(resolution, [status(thm)], [c_393, c_2])).
% 9.57/3.19  tff(c_8923, plain, (![A_410, B_411]: (r2_hidden(k4_tarski(A_410, B_411), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_411, '#skF_10') | ~r2_hidden(A_410, '#skF_9'))), inference(resolution, [status(thm)], [c_58, c_8308])).
% 9.57/3.19  tff(c_46, plain, (![A_49, C_51, B_50, D_52]: (r2_hidden(A_49, C_51) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.57/3.19  tff(c_8950, plain, (![A_410, B_411]: (r2_hidden(A_410, '#skF_11') | ~r2_hidden(B_411, '#skF_10') | ~r2_hidden(A_410, '#skF_9'))), inference(resolution, [status(thm)], [c_8923, c_46])).
% 9.57/3.19  tff(c_8954, plain, (![B_412]: (~r2_hidden(B_412, '#skF_10'))), inference(splitLeft, [status(thm)], [c_8950])).
% 9.57/3.19  tff(c_9022, plain, (r1_xboole_0('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_210, c_8954])).
% 9.57/3.19  tff(c_963, plain, (![A_168, B_169, C_170]: (r2_hidden('#skF_5'(A_168, B_169, C_170), B_169) | r2_hidden('#skF_6'(A_168, B_169, C_170), C_170) | k2_zfmisc_1(A_168, B_169)=C_170)), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.57/3.19  tff(c_14, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.57/3.19  tff(c_84, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.57/3.19  tff(c_88, plain, (![A_13]: (k3_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_84])).
% 9.57/3.19  tff(c_100, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.57/3.19  tff(c_103, plain, (![A_13, C_64]: (~r1_xboole_0(k1_xboole_0, A_13) | ~r2_hidden(C_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88, c_100])).
% 9.57/3.19  tff(c_104, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_103])).
% 9.57/3.19  tff(c_1155, plain, (![A_185, B_186]: (r2_hidden('#skF_5'(A_185, B_186, k1_xboole_0), B_186) | k2_zfmisc_1(A_185, B_186)=k1_xboole_0)), inference(resolution, [status(thm)], [c_963, c_104])).
% 9.57/3.19  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.57/3.19  tff(c_1225, plain, (![A_189, B_190, A_191]: (~r1_xboole_0(A_189, B_190) | k2_zfmisc_1(A_191, k3_xboole_0(A_189, B_190))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1155, c_10])).
% 9.57/3.19  tff(c_48, plain, (![B_54, A_53]: (k1_xboole_0=B_54 | k1_xboole_0=A_53 | k2_zfmisc_1(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.19  tff(c_1298, plain, (![A_189, B_190, A_191]: (k3_xboole_0(A_189, B_190)=k1_xboole_0 | k1_xboole_0=A_191 | ~r1_xboole_0(A_189, B_190))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_48])).
% 9.57/3.19  tff(c_1359, plain, (![A_189, B_190]: (k3_xboole_0(A_189, B_190)=k1_xboole_0 | ~r1_xboole_0(A_189, B_190))), inference(splitLeft, [status(thm)], [c_1298])).
% 9.57/3.19  tff(c_9044, plain, (k3_xboole_0('#skF_10', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_9022, c_1359])).
% 9.57/3.19  tff(c_9073, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_9044])).
% 9.57/3.19  tff(c_99, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_58, c_12])).
% 9.57/3.19  tff(c_170, plain, (![C_10]: (~r1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(C_10, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 9.57/3.19  tff(c_291, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_170])).
% 9.57/3.19  tff(c_207, plain, (r2_hidden('#skF_2'(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_9', '#skF_10')) | r1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_199])).
% 9.57/3.19  tff(c_633, plain, (r2_hidden('#skF_2'(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_291, c_207])).
% 9.57/3.19  tff(c_761, plain, (![A_152, B_153, D_154]: (r2_hidden('#skF_8'(A_152, B_153, k2_zfmisc_1(A_152, B_153), D_154), B_153) | ~r2_hidden(D_154, k2_zfmisc_1(A_152, B_153)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.57/3.19  tff(c_235, plain, (![A_91]: (r2_hidden('#skF_2'(A_91, A_91), A_91) | r1_xboole_0(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_139, c_199])).
% 9.57/3.19  tff(c_449, plain, (![A_119, B_120]: (r2_hidden('#skF_2'(A_119, A_119), B_120) | ~r1_tarski(A_119, B_120) | r1_xboole_0(A_119, A_119))), inference(resolution, [status(thm)], [c_235, c_2])).
% 9.57/3.19  tff(c_463, plain, (![A_121]: (~r1_tarski(A_121, k1_xboole_0) | r1_xboole_0(A_121, A_121))), inference(resolution, [status(thm)], [c_449, c_104])).
% 9.57/3.19  tff(c_140, plain, (![A_73]: (k3_xboole_0(A_73, A_73)=A_73)), inference(resolution, [status(thm)], [c_135, c_12])).
% 9.57/3.19  tff(c_146, plain, (![A_73, C_10]: (~r1_xboole_0(A_73, A_73) | ~r2_hidden(C_10, A_73))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 9.57/3.19  tff(c_475, plain, (![C_10, A_121]: (~r2_hidden(C_10, A_121) | ~r1_tarski(A_121, k1_xboole_0))), inference(resolution, [status(thm)], [c_463, c_146])).
% 9.57/3.19  tff(c_799, plain, (![B_155, D_156, A_157]: (~r1_tarski(B_155, k1_xboole_0) | ~r2_hidden(D_156, k2_zfmisc_1(A_157, B_155)))), inference(resolution, [status(thm)], [c_761, c_475])).
% 9.57/3.19  tff(c_837, plain, (~r1_tarski('#skF_10', k1_xboole_0)), inference(resolution, [status(thm)], [c_633, c_799])).
% 9.57/3.19  tff(c_9141, plain, (~r1_tarski('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_9073, c_837])).
% 9.57/3.19  tff(c_9165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_9141])).
% 9.57/3.19  tff(c_9167, plain, (![A_413]: (r2_hidden(A_413, '#skF_11') | ~r2_hidden(A_413, '#skF_9'))), inference(splitRight, [status(thm)], [c_8950])).
% 9.57/3.19  tff(c_9328, plain, (![A_420]: (r1_tarski(A_420, '#skF_11') | ~r2_hidden('#skF_1'(A_420, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_9167, c_4])).
% 9.57/3.19  tff(c_9336, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_9328])).
% 9.57/3.19  tff(c_9341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_83, c_9336])).
% 9.57/3.19  tff(c_9343, plain, (![A_421]: (k1_xboole_0=A_421)), inference(splitRight, [status(thm)], [c_1298])).
% 9.57/3.19  tff(c_195, plain, (![C_81, B_82, A_83]: (r2_hidden(C_81, B_82) | ~r2_hidden(C_81, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.57/3.19  tff(c_292, plain, (![A_98, B_99, B_100]: (r2_hidden('#skF_1'(A_98, B_99), B_100) | ~r1_tarski(A_98, B_100) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_6, c_195])).
% 9.57/3.19  tff(c_413, plain, (![A_112, B_113, A_114, B_115]: (~r1_xboole_0(A_112, B_113) | ~r1_tarski(A_114, k3_xboole_0(A_112, B_113)) | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_292, c_10])).
% 9.57/3.19  tff(c_422, plain, (![A_72, A_114, B_115]: (~r1_xboole_0(A_72, A_72) | ~r1_tarski(A_114, A_72) | r1_tarski(A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_139, c_413])).
% 9.57/3.19  tff(c_645, plain, (![A_137, A_138, B_139]: (~r1_tarski(A_137, A_138) | r1_tarski(A_137, B_139) | ~r1_tarski(A_138, k1_xboole_0))), inference(resolution, [status(thm)], [c_463, c_422])).
% 9.57/3.19  tff(c_659, plain, (![B_139]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), B_139) | ~r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_645])).
% 9.57/3.19  tff(c_884, plain, (~r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_659])).
% 9.57/3.19  tff(c_9377, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9343, c_884])).
% 9.57/3.19  tff(c_9530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_9377])).
% 9.57/3.19  tff(c_9531, plain, (![B_139]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), B_139))), inference(splitRight, [status(thm)], [c_659])).
% 9.57/3.19  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.57/3.19  tff(c_476, plain, (![C_122, A_123]: (~r2_hidden(C_122, A_123) | ~r1_tarski(A_123, k1_xboole_0))), inference(resolution, [status(thm)], [c_463, c_146])).
% 9.57/3.19  tff(c_516, plain, (![A_126, B_127]: (~r1_tarski(k3_xboole_0(A_126, B_127), k1_xboole_0) | r1_xboole_0(A_126, B_127))), inference(resolution, [status(thm)], [c_8, c_476])).
% 9.57/3.19  tff(c_526, plain, (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k1_xboole_0) | r1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_516])).
% 9.57/3.19  tff(c_534, plain, (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_291, c_526])).
% 9.57/3.19  tff(c_9536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9531, c_534])).
% 9.57/3.19  tff(c_9537, plain, (![C_10]: (~r2_hidden(C_10, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(splitRight, [status(thm)], [c_170])).
% 9.57/3.19  tff(c_9619, plain, (![B_2361, A_2360]: (~r2_hidden(B_2361, '#skF_10') | ~r2_hidden(A_2360, '#skF_9'))), inference(resolution, [status(thm)], [c_9600, c_9537])).
% 9.57/3.19  tff(c_9638, plain, (![A_2365]: (~r2_hidden(A_2365, '#skF_9'))), inference(splitLeft, [status(thm)], [c_9619])).
% 9.57/3.19  tff(c_9648, plain, (![B_2]: (r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_6, c_9638])).
% 9.57/3.19  tff(c_9659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9648, c_83])).
% 9.57/3.19  tff(c_9660, plain, (![B_2361]: (~r2_hidden(B_2361, '#skF_10'))), inference(splitRight, [status(thm)], [c_9619])).
% 9.57/3.19  tff(c_11315, plain, (![A_2511, B_2512]: (r2_hidden('#skF_5'(A_2511, B_2512, '#skF_10'), B_2512) | k2_zfmisc_1(A_2511, B_2512)='#skF_10')), inference(resolution, [status(thm)], [c_10398, c_9660])).
% 9.57/3.19  tff(c_11400, plain, (![A_2511]: (k2_zfmisc_1(A_2511, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_11315, c_9660])).
% 9.57/3.19  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.57/3.19  tff(c_11421, plain, (k1_xboole_0!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11400, c_56])).
% 9.57/3.19  tff(c_11432, plain, (![A_2513]: (k2_zfmisc_1(A_2513, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_11315, c_9660])).
% 9.57/3.19  tff(c_52, plain, (![B_54]: (k2_zfmisc_1(k1_xboole_0, B_54)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.19  tff(c_11540, plain, (k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_11432, c_52])).
% 9.57/3.19  tff(c_11573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11421, c_11540])).
% 9.57/3.19  tff(c_11575, plain, (![A_2514]: (~r1_xboole_0(k1_xboole_0, A_2514))), inference(splitRight, [status(thm)], [c_103])).
% 9.57/3.19  tff(c_11580, plain, $false, inference(resolution, [status(thm)], [c_16, c_11575])).
% 9.57/3.19  tff(c_11581, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_54])).
% 9.57/3.19  tff(c_11948, plain, (![A_2567, B_2568, C_2569, D_2570]: (r2_hidden(k4_tarski(A_2567, B_2568), k2_zfmisc_1(C_2569, D_2570)) | ~r2_hidden(B_2568, D_2570) | ~r2_hidden(A_2567, C_2569))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.57/3.19  tff(c_16934, plain, (![B_2836, B_2835, A_2838, D_2834, C_2837]: (r2_hidden(k4_tarski(A_2838, B_2835), B_2836) | ~r1_tarski(k2_zfmisc_1(C_2837, D_2834), B_2836) | ~r2_hidden(B_2835, D_2834) | ~r2_hidden(A_2838, C_2837))), inference(resolution, [status(thm)], [c_11948, c_2])).
% 9.57/3.19  tff(c_17066, plain, (![A_2844, B_2845]: (r2_hidden(k4_tarski(A_2844, B_2845), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_2845, '#skF_10') | ~r2_hidden(A_2844, '#skF_9'))), inference(resolution, [status(thm)], [c_58, c_16934])).
% 9.57/3.19  tff(c_44, plain, (![B_50, D_52, A_49, C_51]: (r2_hidden(B_50, D_52) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.57/3.19  tff(c_17094, plain, (![B_2845, A_2844]: (r2_hidden(B_2845, '#skF_12') | ~r2_hidden(B_2845, '#skF_10') | ~r2_hidden(A_2844, '#skF_9'))), inference(resolution, [status(thm)], [c_17066, c_44])).
% 9.57/3.19  tff(c_17528, plain, (![A_2844]: (~r2_hidden(A_2844, '#skF_9'))), inference(splitLeft, [status(thm)], [c_17094])).
% 9.57/3.19  tff(c_11582, plain, (r1_tarski('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_54])).
% 9.57/3.19  tff(c_11583, plain, (![A_2515, B_2516]: (k3_xboole_0(A_2515, B_2516)=A_2515 | ~r1_tarski(A_2515, B_2516))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.57/3.19  tff(c_11594, plain, (k3_xboole_0('#skF_9', '#skF_11')='#skF_9'), inference(resolution, [status(thm)], [c_11582, c_11583])).
% 9.57/3.19  tff(c_11612, plain, (![A_2520, B_2521, C_2522]: (~r1_xboole_0(A_2520, B_2521) | ~r2_hidden(C_2522, k3_xboole_0(A_2520, B_2521)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.57/3.19  tff(c_11621, plain, (![C_2522]: (~r1_xboole_0('#skF_9', '#skF_11') | ~r2_hidden(C_2522, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_11594, c_11612])).
% 9.57/3.19  tff(c_11635, plain, (~r1_xboole_0('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_11621])).
% 9.57/3.19  tff(c_11722, plain, (![A_2544, B_2545]: (r2_hidden('#skF_2'(A_2544, B_2545), k3_xboole_0(A_2544, B_2545)) | r1_xboole_0(A_2544, B_2545))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.57/3.19  tff(c_11739, plain, (r2_hidden('#skF_2'('#skF_9', '#skF_11'), '#skF_9') | r1_xboole_0('#skF_9', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_11594, c_11722])).
% 9.57/3.19  tff(c_11744, plain, (r2_hidden('#skF_2'('#skF_9', '#skF_11'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_11635, c_11739])).
% 9.57/3.19  tff(c_17530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17528, c_11744])).
% 9.57/3.19  tff(c_17532, plain, (![B_2855]: (r2_hidden(B_2855, '#skF_12') | ~r2_hidden(B_2855, '#skF_10'))), inference(splitRight, [status(thm)], [c_17094])).
% 9.57/3.19  tff(c_17951, plain, (![B_2863]: (r2_hidden('#skF_1'('#skF_10', B_2863), '#skF_12') | r1_tarski('#skF_10', B_2863))), inference(resolution, [status(thm)], [c_6, c_17532])).
% 9.57/3.19  tff(c_17960, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_17951, c_4])).
% 9.57/3.19  tff(c_17966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11581, c_11581, c_17960])).
% 9.57/3.19  tff(c_17967, plain, (![C_2522]: (~r2_hidden(C_2522, '#skF_9'))), inference(splitRight, [status(thm)], [c_11621])).
% 9.57/3.19  tff(c_20770, plain, (![A_3087, B_3088]: (r2_hidden('#skF_5'(A_3087, B_3088, '#skF_9'), B_3088) | k2_zfmisc_1(A_3087, B_3088)='#skF_9')), inference(resolution, [status(thm)], [c_20089, c_17967])).
% 9.57/3.19  tff(c_20853, plain, (![A_3089]: (k2_zfmisc_1(A_3089, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_20770, c_17967])).
% 9.57/3.19  tff(c_20933, plain, (k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_20853, c_52])).
% 9.57/3.19  tff(c_20962, plain, (![B_54]: (k2_zfmisc_1('#skF_9', B_54)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20933, c_20933, c_52])).
% 9.57/3.19  tff(c_20964, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_20933, c_56])).
% 9.57/3.19  tff(c_21088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20962, c_20964])).
% 9.57/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.19  
% 9.57/3.19  Inference rules
% 9.57/3.19  ----------------------
% 9.57/3.19  #Ref     : 0
% 9.57/3.19  #Sup     : 5092
% 9.57/3.19  #Fact    : 0
% 9.57/3.19  #Define  : 0
% 9.57/3.19  #Split   : 18
% 9.57/3.19  #Chain   : 0
% 9.57/3.19  #Close   : 0
% 9.63/3.19  
% 9.63/3.19  Ordering : KBO
% 9.63/3.19  
% 9.63/3.19  Simplification rules
% 9.63/3.19  ----------------------
% 9.63/3.19  #Subsume      : 2022
% 9.63/3.19  #Demod        : 2711
% 9.63/3.19  #Tautology    : 1730
% 9.63/3.19  #SimpNegUnit  : 90
% 9.63/3.19  #BackRed      : 280
% 9.63/3.19  
% 9.63/3.19  #Partial instantiations: 252
% 9.63/3.19  #Strategies tried      : 1
% 9.63/3.19  
% 9.63/3.19  Timing (in seconds)
% 9.63/3.19  ----------------------
% 9.63/3.19  Preprocessing        : 0.29
% 9.63/3.19  Parsing              : 0.15
% 9.63/3.19  CNF conversion       : 0.03
% 9.63/3.19  Main loop            : 2.11
% 9.63/3.19  Inferencing          : 0.68
% 9.63/3.19  Reduction            : 0.65
% 9.63/3.19  Demodulation         : 0.47
% 9.63/3.19  BG Simplification    : 0.07
% 9.63/3.19  Subsumption          : 0.55
% 9.63/3.19  Abstraction          : 0.10
% 9.63/3.19  MUC search           : 0.00
% 9.63/3.19  Cooper               : 0.00
% 9.63/3.19  Total                : 2.45
% 9.63/3.19  Index Insertion      : 0.00
% 9.63/3.19  Index Deletion       : 0.00
% 9.63/3.19  Index Matching       : 0.00
% 9.63/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
