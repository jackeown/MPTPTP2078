%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:00 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 178 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 252 expanded)
%              Number of equality atoms :   35 (  92 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_26,plain,(
    ! [A_23] : k1_subset_1(A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_49,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_46])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_22,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    ! [A_20] : r1_tarski('#skF_4',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_22])).

tff(c_40,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_40])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_117,c_50])).

tff(c_194,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_371,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_375,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_371,c_6])).

tff(c_193,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_228,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_235,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_193,c_228])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k3_xboole_0(A_14,B_15),k5_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_316,plain,(
    r1_xboole_0('#skF_4',k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_16])).

tff(c_540,plain,(
    ! [B_80,A_81] :
      ( ~ r1_xboole_0(B_80,A_81)
      | ~ r1_tarski(B_80,A_81)
      | v1_xboole_0(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_566,plain,
    ( ~ r1_tarski('#skF_4',k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_316,c_540])).

tff(c_773,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_997,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_375,c_773])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = k2_subset_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_48,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_xboole_0) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_47])).

tff(c_967,plain,(
    ! [C_97,A_98,B_99] :
      ( r1_tarski(C_97,k3_subset_1(A_98,B_99))
      | ~ r1_tarski(B_99,k3_subset_1(A_98,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_980,plain,(
    ! [C_97,A_98] :
      ( r1_tarski(C_97,k3_subset_1(A_98,k1_xboole_0))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_98)) ) ),
    inference(resolution,[status(thm)],[c_22,c_967])).

tff(c_1002,plain,(
    ! [C_100,A_101] :
      ( r1_tarski(C_100,A_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_48,c_980])).

tff(c_1009,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1002])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1015,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1009,c_20])).

tff(c_776,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,B_91) = k3_subset_1(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_783,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_776])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_386,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1072,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(B_104,A_103)) = k4_xboole_0(A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_386])).

tff(c_1095,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_1072])).

tff(c_1127,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1095])).

tff(c_291,plain,(
    ! [A_57,B_58] : r1_xboole_0(k3_xboole_0(A_57,B_58),k5_xboole_0(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_303,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_291])).

tff(c_1138,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_303])).

tff(c_1156,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1138])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( ~ r1_xboole_0(B_22,A_21)
      | ~ r1_tarski(B_22,A_21)
      | v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1161,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1156,c_24])).

tff(c_1164,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1161])).

tff(c_1166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_1164])).

tff(c_1167,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_376,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_371,c_6])).

tff(c_380,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_376,c_20])).

tff(c_1177,plain,(
    ! [B_105] : k3_xboole_0('#skF_4',B_105) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1167,c_380])).

tff(c_237,plain,(
    ! [A_55] : k3_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_242,plain,(
    ! [A_55] : k3_xboole_0(A_55,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2])).

tff(c_1195,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_242])).

tff(c_1222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_1195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.71/1.43  
% 2.71/1.43  %Foreground sorts:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Background operators:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Foreground operators:
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.71/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.43  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.71/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.71/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.43  
% 2.71/1.44  tff(f_62, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.71/1.44  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.71/1.44  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.71/1.44  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.44  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.71/1.44  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.71/1.44  tff(f_44, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.71/1.44  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.71/1.44  tff(f_81, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.71/1.44  tff(f_64, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.71/1.44  tff(f_70, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.71/1.44  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.71/1.44  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.71/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.71/1.44  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.71/1.44  tff(c_26, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.71/1.44  tff(c_46, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.71/1.44  tff(c_49, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_46])).
% 2.71/1.44  tff(c_117, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_49])).
% 2.71/1.44  tff(c_22, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.44  tff(c_121, plain, (![A_20]: (r1_tarski('#skF_4', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_22])).
% 2.71/1.44  tff(c_40, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.71/1.44  tff(c_50, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_40])).
% 2.71/1.44  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_117, c_50])).
% 2.71/1.44  tff(c_194, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_49])).
% 2.71/1.44  tff(c_371, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.44  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.44  tff(c_375, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_371, c_6])).
% 2.71/1.44  tff(c_193, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_49])).
% 2.71/1.44  tff(c_228, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.44  tff(c_235, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_193, c_228])).
% 2.71/1.44  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k3_xboole_0(A_14, B_15), k5_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.44  tff(c_316, plain, (r1_xboole_0('#skF_4', k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_235, c_16])).
% 2.71/1.44  tff(c_540, plain, (![B_80, A_81]: (~r1_xboole_0(B_80, A_81) | ~r1_tarski(B_80, A_81) | v1_xboole_0(B_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.44  tff(c_566, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_316, c_540])).
% 2.71/1.44  tff(c_773, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_566])).
% 2.71/1.44  tff(c_997, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_375, c_773])).
% 2.71/1.44  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.71/1.44  tff(c_36, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.71/1.44  tff(c_28, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.44  tff(c_32, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=k2_subset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.44  tff(c_47, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.71/1.44  tff(c_48, plain, (![A_27]: (k3_subset_1(A_27, k1_xboole_0)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_47])).
% 2.71/1.44  tff(c_967, plain, (![C_97, A_98, B_99]: (r1_tarski(C_97, k3_subset_1(A_98, B_99)) | ~r1_tarski(B_99, k3_subset_1(A_98, C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.44  tff(c_980, plain, (![C_97, A_98]: (r1_tarski(C_97, k3_subset_1(A_98, k1_xboole_0)) | ~m1_subset_1(C_97, k1_zfmisc_1(A_98)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_98)))), inference(resolution, [status(thm)], [c_22, c_967])).
% 2.71/1.44  tff(c_1002, plain, (![C_100, A_101]: (r1_tarski(C_100, A_101) | ~m1_subset_1(C_100, k1_zfmisc_1(A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_48, c_980])).
% 2.71/1.44  tff(c_1009, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_1002])).
% 2.71/1.44  tff(c_20, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.44  tff(c_1015, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1009, c_20])).
% 2.71/1.44  tff(c_776, plain, (![A_90, B_91]: (k4_xboole_0(A_90, B_91)=k3_subset_1(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.44  tff(c_783, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_776])).
% 2.71/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.44  tff(c_386, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.44  tff(c_1072, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(B_104, A_103))=k4_xboole_0(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_2, c_386])).
% 2.71/1.44  tff(c_1095, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1015, c_1072])).
% 2.71/1.44  tff(c_1127, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_1095])).
% 2.71/1.44  tff(c_291, plain, (![A_57, B_58]: (r1_xboole_0(k3_xboole_0(A_57, B_58), k5_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.44  tff(c_303, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_291])).
% 2.71/1.44  tff(c_1138, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1127, c_303])).
% 2.71/1.44  tff(c_1156, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1138])).
% 2.71/1.44  tff(c_24, plain, (![B_22, A_21]: (~r1_xboole_0(B_22, A_21) | ~r1_tarski(B_22, A_21) | v1_xboole_0(B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.44  tff(c_1161, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1156, c_24])).
% 2.71/1.44  tff(c_1164, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_1161])).
% 2.71/1.44  tff(c_1166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_997, c_1164])).
% 2.71/1.44  tff(c_1167, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_566])).
% 2.71/1.44  tff(c_376, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_371, c_6])).
% 2.71/1.44  tff(c_380, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_376, c_20])).
% 2.71/1.44  tff(c_1177, plain, (![B_105]: (k3_xboole_0('#skF_4', B_105)='#skF_4')), inference(resolution, [status(thm)], [c_1167, c_380])).
% 2.71/1.44  tff(c_237, plain, (![A_55]: (k3_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_228])).
% 2.71/1.44  tff(c_242, plain, (![A_55]: (k3_xboole_0(A_55, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_237, c_2])).
% 2.71/1.44  tff(c_1195, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1177, c_242])).
% 2.71/1.44  tff(c_1222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_1195])).
% 2.71/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  Inference rules
% 2.71/1.44  ----------------------
% 2.71/1.44  #Ref     : 0
% 2.71/1.44  #Sup     : 283
% 2.71/1.44  #Fact    : 0
% 2.71/1.44  #Define  : 0
% 2.71/1.44  #Split   : 2
% 2.71/1.44  #Chain   : 0
% 2.71/1.44  #Close   : 0
% 2.71/1.44  
% 2.71/1.44  Ordering : KBO
% 2.71/1.44  
% 2.71/1.44  Simplification rules
% 2.71/1.44  ----------------------
% 2.71/1.44  #Subsume      : 30
% 2.71/1.44  #Demod        : 163
% 2.71/1.44  #Tautology    : 192
% 2.71/1.44  #SimpNegUnit  : 3
% 2.71/1.44  #BackRed      : 12
% 2.71/1.44  
% 2.71/1.44  #Partial instantiations: 0
% 2.71/1.44  #Strategies tried      : 1
% 2.71/1.44  
% 2.71/1.44  Timing (in seconds)
% 2.71/1.44  ----------------------
% 2.71/1.45  Preprocessing        : 0.31
% 2.71/1.45  Parsing              : 0.16
% 2.71/1.45  CNF conversion       : 0.02
% 2.71/1.45  Main loop            : 0.37
% 2.71/1.45  Inferencing          : 0.13
% 2.71/1.45  Reduction            : 0.14
% 2.71/1.45  Demodulation         : 0.11
% 2.71/1.45  BG Simplification    : 0.02
% 2.71/1.45  Subsumption          : 0.06
% 2.71/1.45  Abstraction          : 0.02
% 2.71/1.45  MUC search           : 0.00
% 2.71/1.45  Cooper               : 0.00
% 2.71/1.45  Total                : 0.71
% 2.71/1.45  Index Insertion      : 0.00
% 2.71/1.45  Index Deletion       : 0.00
% 2.71/1.45  Index Matching       : 0.00
% 2.71/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
