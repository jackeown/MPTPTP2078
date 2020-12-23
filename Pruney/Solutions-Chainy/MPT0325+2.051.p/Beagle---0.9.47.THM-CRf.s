%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 200 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 356 expanded)
%              Number of equality atoms :   76 ( 153 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_874,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(A_126,B_127)
      | k4_xboole_0(A_126,B_127) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_50,plain,(
    k4_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_44])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_109,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( ~ r1_xboole_0(A_54,B_55)
      | r1_xboole_0(k2_zfmisc_1(A_54,C_56),k2_zfmisc_1(B_55,D_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    ! [A_66,C_67,B_68,D_69] :
      ( k3_xboole_0(k2_zfmisc_1(A_66,C_67),k2_zfmisc_1(B_68,D_69)) = k1_xboole_0
      | ~ r1_xboole_0(A_66,B_68) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_36,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_52])).

tff(c_173,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_60])).

tff(c_194,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_173])).

tff(c_201,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_104,plain,(
    ! [C_50,D_51,A_52,B_53] :
      ( ~ r1_xboole_0(C_50,D_51)
      | r1_xboole_0(k2_zfmisc_1(A_52,C_50),k2_zfmisc_1(B_53,D_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,(
    ! [A_58,C_59,B_60,D_61] :
      ( k3_xboole_0(k2_zfmisc_1(A_58,C_59),k2_zfmisc_1(B_60,D_61)) = k1_xboole_0
      | ~ r1_xboole_0(C_59,D_61) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_135,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_60])).

tff(c_152,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_135])).

tff(c_158,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_369,plain,(
    ! [A_99,C_100,B_101,D_102] : k3_xboole_0(k2_zfmisc_1(A_99,C_100),k2_zfmisc_1(B_101,D_102)) = k2_zfmisc_1(k3_xboole_0(A_99,B_101),k3_xboole_0(C_100,D_102)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_375,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_60])).

tff(c_30,plain,(
    ! [C_27,A_25,B_26,D_28] :
      ( C_27 = A_25
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | k2_zfmisc_1(C_27,D_28) != k2_zfmisc_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_405,plain,(
    ! [C_27,D_28] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_27
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0
      | k2_zfmisc_1(C_27,D_28) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_30])).

tff(c_428,plain,(
    ! [C_27,D_28] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_27
      | k2_zfmisc_1(C_27,D_28) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_158,c_405])).

tff(c_762,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_428])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_862,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_16])).

tff(c_867,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_862])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_867])).

tff(c_870,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_878,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_874,c_870])).

tff(c_871,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_879,plain,(
    ! [A_128,B_129] :
      ( k3_xboole_0(A_128,B_129) = A_128
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_891,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_871,c_879])).

tff(c_922,plain,(
    ! [A_134,B_135,C_136] :
      ( ~ r1_xboole_0(A_134,B_135)
      | ~ r2_hidden(C_136,k3_xboole_0(A_134,B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_925,plain,(
    ! [C_136] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_136,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_922])).

tff(c_951,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_925])).

tff(c_954,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_951])).

tff(c_956,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_954])).

tff(c_990,plain,(
    ! [C_147,D_148,A_149,B_150] :
      ( ~ r1_xboole_0(C_147,D_148)
      | r1_xboole_0(k2_zfmisc_1(A_149,C_147),k2_zfmisc_1(B_150,D_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1021,plain,(
    ! [A_155,C_156,B_157,D_158] :
      ( k3_xboole_0(k2_zfmisc_1(A_155,C_156),k2_zfmisc_1(B_157,D_158)) = k1_xboole_0
      | ~ r1_xboole_0(C_156,D_158) ) ),
    inference(resolution,[status(thm)],[c_990,c_2])).

tff(c_890,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_879])).

tff(c_1039,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_890])).

tff(c_1051,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1039])).

tff(c_1058,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1051])).

tff(c_1085,plain,(
    ! [A_167,C_168,B_169,D_170] : k3_xboole_0(k2_zfmisc_1(A_167,C_168),k2_zfmisc_1(B_169,D_170)) = k2_zfmisc_1(k3_xboole_0(A_167,B_169),k3_xboole_0(C_168,D_170)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1100,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_890])).

tff(c_1108,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_1100])).

tff(c_28,plain,(
    ! [D_28,B_26,A_25,C_27] :
      ( D_28 = B_26
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | k2_zfmisc_1(C_27,D_28) != k2_zfmisc_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1123,plain,(
    ! [D_28,C_27] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_28
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1(C_27,D_28) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_28])).

tff(c_1146,plain,(
    ! [D_28,C_27] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_28
      | k2_zfmisc_1(C_27,D_28) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_956,c_1058,c_1123])).

tff(c_1162,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1146])).

tff(c_1177,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_16])).

tff(c_1184,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1177])).

tff(c_1186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_1184])).

tff(c_1189,plain,(
    ! [C_175] : ~ r2_hidden(C_175,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_1194,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_1189])).

tff(c_1203,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_34])).

tff(c_1188,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_1302,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( ~ r1_xboole_0(A_194,B_195)
      | r1_xboole_0(k2_zfmisc_1(A_194,C_196),k2_zfmisc_1(B_195,D_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1197,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_3'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_2])).

tff(c_1344,plain,(
    ! [A_206,C_207,B_208,D_209] :
      ( k3_xboole_0(k2_zfmisc_1(A_206,C_207),k2_zfmisc_1(B_208,D_209)) = '#skF_3'
      | ~ r1_xboole_0(A_206,B_208) ) ),
    inference(resolution,[status(thm)],[c_1302,c_1197])).

tff(c_1362,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_3'
    | ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_890])).

tff(c_1376,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1362])).

tff(c_1378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1203,c_1376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.15/1.50  
% 3.15/1.50  %Foreground sorts:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Background operators:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Foreground operators:
% 3.15/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.51  
% 3.36/1.52  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.36/1.52  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.36/1.52  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 3.36/1.52  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.36/1.52  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.36/1.52  tff(f_71, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.36/1.52  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.36/1.52  tff(f_65, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.36/1.52  tff(f_81, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.36/1.52  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.36/1.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.36/1.52  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.52  tff(c_874, plain, (![A_126, B_127]: (r1_tarski(A_126, B_127) | k4_xboole_0(A_126, B_127)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.52  tff(c_46, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.52  tff(c_32, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.36/1.52  tff(c_44, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 3.36/1.52  tff(c_50, plain, (k4_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_44])).
% 3.36/1.52  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.52  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.52  tff(c_34, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.36/1.52  tff(c_109, plain, (![A_54, B_55, C_56, D_57]: (~r1_xboole_0(A_54, B_55) | r1_xboole_0(k2_zfmisc_1(A_54, C_56), k2_zfmisc_1(B_55, D_57)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.36/1.52  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.52  tff(c_164, plain, (![A_66, C_67, B_68, D_69]: (k3_xboole_0(k2_zfmisc_1(A_66, C_67), k2_zfmisc_1(B_68, D_69))=k1_xboole_0 | ~r1_xboole_0(A_66, B_68))), inference(resolution, [status(thm)], [c_109, c_2])).
% 3.36/1.52  tff(c_36, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.36/1.52  tff(c_52, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.52  tff(c_60, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_52])).
% 3.36/1.52  tff(c_173, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_164, c_60])).
% 3.36/1.52  tff(c_194, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_173])).
% 3.36/1.52  tff(c_201, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_194])).
% 3.36/1.52  tff(c_104, plain, (![C_50, D_51, A_52, B_53]: (~r1_xboole_0(C_50, D_51) | r1_xboole_0(k2_zfmisc_1(A_52, C_50), k2_zfmisc_1(B_53, D_51)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.36/1.52  tff(c_129, plain, (![A_58, C_59, B_60, D_61]: (k3_xboole_0(k2_zfmisc_1(A_58, C_59), k2_zfmisc_1(B_60, D_61))=k1_xboole_0 | ~r1_xboole_0(C_59, D_61))), inference(resolution, [status(thm)], [c_104, c_2])).
% 3.36/1.52  tff(c_135, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_129, c_60])).
% 3.36/1.52  tff(c_152, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_34, c_135])).
% 3.36/1.52  tff(c_158, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_152])).
% 3.36/1.52  tff(c_369, plain, (![A_99, C_100, B_101, D_102]: (k3_xboole_0(k2_zfmisc_1(A_99, C_100), k2_zfmisc_1(B_101, D_102))=k2_zfmisc_1(k3_xboole_0(A_99, B_101), k3_xboole_0(C_100, D_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.52  tff(c_375, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_369, c_60])).
% 3.36/1.52  tff(c_30, plain, (![C_27, A_25, B_26, D_28]: (C_27=A_25 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | k2_zfmisc_1(C_27, D_28)!=k2_zfmisc_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.52  tff(c_405, plain, (![C_27, D_28]: (k3_xboole_0('#skF_3', '#skF_5')=C_27 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k2_zfmisc_1(C_27, D_28)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_30])).
% 3.36/1.52  tff(c_428, plain, (![C_27, D_28]: (k3_xboole_0('#skF_3', '#skF_5')=C_27 | k2_zfmisc_1(C_27, D_28)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_201, c_158, c_405])).
% 3.36/1.52  tff(c_762, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_428])).
% 3.36/1.52  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.52  tff(c_862, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_762, c_16])).
% 3.36/1.52  tff(c_867, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_862])).
% 3.36/1.52  tff(c_869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_867])).
% 3.36/1.52  tff(c_870, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 3.36/1.52  tff(c_878, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_874, c_870])).
% 3.36/1.52  tff(c_871, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 3.36/1.52  tff(c_879, plain, (![A_128, B_129]: (k3_xboole_0(A_128, B_129)=A_128 | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.52  tff(c_891, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_871, c_879])).
% 3.36/1.52  tff(c_922, plain, (![A_134, B_135, C_136]: (~r1_xboole_0(A_134, B_135) | ~r2_hidden(C_136, k3_xboole_0(A_134, B_135)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.52  tff(c_925, plain, (![C_136]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_136, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_891, c_922])).
% 3.36/1.52  tff(c_951, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_925])).
% 3.36/1.52  tff(c_954, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_951])).
% 3.36/1.52  tff(c_956, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_891, c_954])).
% 3.36/1.52  tff(c_990, plain, (![C_147, D_148, A_149, B_150]: (~r1_xboole_0(C_147, D_148) | r1_xboole_0(k2_zfmisc_1(A_149, C_147), k2_zfmisc_1(B_150, D_148)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.36/1.52  tff(c_1021, plain, (![A_155, C_156, B_157, D_158]: (k3_xboole_0(k2_zfmisc_1(A_155, C_156), k2_zfmisc_1(B_157, D_158))=k1_xboole_0 | ~r1_xboole_0(C_156, D_158))), inference(resolution, [status(thm)], [c_990, c_2])).
% 3.36/1.52  tff(c_890, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_879])).
% 3.36/1.52  tff(c_1039, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_890])).
% 3.36/1.52  tff(c_1051, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_34, c_1039])).
% 3.36/1.52  tff(c_1058, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_1051])).
% 3.36/1.52  tff(c_1085, plain, (![A_167, C_168, B_169, D_170]: (k3_xboole_0(k2_zfmisc_1(A_167, C_168), k2_zfmisc_1(B_169, D_170))=k2_zfmisc_1(k3_xboole_0(A_167, B_169), k3_xboole_0(C_168, D_170)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.52  tff(c_1100, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1085, c_890])).
% 3.36/1.52  tff(c_1108, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_891, c_1100])).
% 3.36/1.52  tff(c_28, plain, (![D_28, B_26, A_25, C_27]: (D_28=B_26 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | k2_zfmisc_1(C_27, D_28)!=k2_zfmisc_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.52  tff(c_1123, plain, (![D_28, C_27]: (k3_xboole_0('#skF_4', '#skF_6')=D_28 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1(C_27, D_28)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1108, c_28])).
% 3.36/1.52  tff(c_1146, plain, (![D_28, C_27]: (k3_xboole_0('#skF_4', '#skF_6')=D_28 | k2_zfmisc_1(C_27, D_28)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_956, c_1058, c_1123])).
% 3.36/1.52  tff(c_1162, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_1146])).
% 3.36/1.52  tff(c_1177, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1162, c_16])).
% 3.36/1.52  tff(c_1184, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1177])).
% 3.36/1.52  tff(c_1186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_1184])).
% 3.36/1.52  tff(c_1189, plain, (![C_175]: (~r2_hidden(C_175, '#skF_3'))), inference(splitRight, [status(thm)], [c_925])).
% 3.36/1.52  tff(c_1194, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10, c_1189])).
% 3.36/1.52  tff(c_1203, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_34])).
% 3.36/1.52  tff(c_1188, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_925])).
% 3.36/1.52  tff(c_1302, plain, (![A_194, B_195, C_196, D_197]: (~r1_xboole_0(A_194, B_195) | r1_xboole_0(k2_zfmisc_1(A_194, C_196), k2_zfmisc_1(B_195, D_197)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.36/1.52  tff(c_1197, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_3' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_2])).
% 3.36/1.52  tff(c_1344, plain, (![A_206, C_207, B_208, D_209]: (k3_xboole_0(k2_zfmisc_1(A_206, C_207), k2_zfmisc_1(B_208, D_209))='#skF_3' | ~r1_xboole_0(A_206, B_208))), inference(resolution, [status(thm)], [c_1302, c_1197])).
% 3.36/1.52  tff(c_1362, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_3' | ~r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1344, c_890])).
% 3.36/1.52  tff(c_1376, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1362])).
% 3.36/1.52  tff(c_1378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1203, c_1376])).
% 3.36/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.52  
% 3.36/1.52  Inference rules
% 3.36/1.52  ----------------------
% 3.36/1.52  #Ref     : 11
% 3.36/1.52  #Sup     : 356
% 3.36/1.52  #Fact    : 0
% 3.36/1.52  #Define  : 0
% 3.36/1.52  #Split   : 5
% 3.36/1.52  #Chain   : 0
% 3.36/1.52  #Close   : 0
% 3.36/1.52  
% 3.36/1.52  Ordering : KBO
% 3.36/1.52  
% 3.36/1.52  Simplification rules
% 3.36/1.52  ----------------------
% 3.36/1.52  #Subsume      : 92
% 3.36/1.52  #Demod        : 69
% 3.36/1.52  #Tautology    : 116
% 3.36/1.52  #SimpNegUnit  : 46
% 3.36/1.52  #BackRed      : 26
% 3.36/1.52  
% 3.36/1.52  #Partial instantiations: 0
% 3.36/1.52  #Strategies tried      : 1
% 3.36/1.52  
% 3.36/1.52  Timing (in seconds)
% 3.36/1.52  ----------------------
% 3.36/1.53  Preprocessing        : 0.30
% 3.36/1.53  Parsing              : 0.16
% 3.36/1.53  CNF conversion       : 0.02
% 3.36/1.53  Main loop            : 0.45
% 3.36/1.53  Inferencing          : 0.17
% 3.36/1.53  Reduction            : 0.13
% 3.36/1.53  Demodulation         : 0.09
% 3.36/1.53  BG Simplification    : 0.02
% 3.36/1.53  Subsumption          : 0.08
% 3.36/1.53  Abstraction          : 0.03
% 3.36/1.53  MUC search           : 0.00
% 3.36/1.53  Cooper               : 0.00
% 3.36/1.53  Total                : 0.79
% 3.36/1.53  Index Insertion      : 0.00
% 3.36/1.53  Index Deletion       : 0.00
% 3.36/1.53  Index Matching       : 0.00
% 3.36/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
