%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 8.45s
% Output     : CNFRefutation 8.45s
% Verified   : 
% Statistics : Number of formulae       :   86 (  95 expanded)
%              Number of leaves         :   46 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 112 expanded)
%              Number of equality atoms :   38 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_72,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_62,plain,(
    ! [A_69] : k2_subset_1(A_69) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_72,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_75,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_72])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    ! [A_74] : ~ v1_xboole_0(k1_zfmisc_1(A_74)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [A_66] : k3_tarski(k1_zfmisc_1(A_66)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [B_68,A_67] :
      ( r2_hidden(B_68,A_67)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_463,plain,(
    ! [C_131,A_132,D_133] :
      ( r2_hidden(C_131,k3_tarski(A_132))
      | ~ r2_hidden(D_133,A_132)
      | ~ r2_hidden(C_131,D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_618,plain,(
    ! [C_165,A_166,B_167] :
      ( r2_hidden(C_165,k3_tarski(A_166))
      | ~ r2_hidden(C_165,B_167)
      | ~ m1_subset_1(B_167,A_166)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_56,c_463])).

tff(c_1051,plain,(
    ! [A_217,B_218,A_219] :
      ( r2_hidden('#skF_1'(A_217,B_218),k3_tarski(A_219))
      | ~ m1_subset_1(A_217,A_219)
      | v1_xboole_0(A_219)
      | r1_tarski(A_217,B_218) ) ),
    inference(resolution,[status(thm)],[c_8,c_618])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1089,plain,(
    ! [A_223,A_224] :
      ( ~ m1_subset_1(A_223,A_224)
      | v1_xboole_0(A_224)
      | r1_tarski(A_223,k3_tarski(A_224)) ) ),
    inference(resolution,[status(thm)],[c_1051,c_6])).

tff(c_1113,plain,(
    ! [A_223,A_66] :
      ( ~ m1_subset_1(A_223,k1_zfmisc_1(A_66))
      | v1_xboole_0(k1_zfmisc_1(A_66))
      | r1_tarski(A_223,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1089])).

tff(c_1120,plain,(
    ! [A_225,A_226] :
      ( ~ m1_subset_1(A_225,k1_zfmisc_1(A_226))
      | r1_tarski(A_225,A_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1113])).

tff(c_1158,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_1120])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1169,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1158,c_14])).

tff(c_104,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_84,B_83] : k2_xboole_0(A_84,k3_xboole_0(B_83,A_84)) = A_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12])).

tff(c_1179,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_119])).

tff(c_18,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_204,plain,(
    ! [A_89,B_90] : k3_tarski(k2_tarski(A_89,B_90)) = k2_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_240,plain,(
    ! [B_101,A_102] : k3_tarski(k2_tarski(B_101,A_102)) = k2_xboole_0(A_102,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_204])).

tff(c_50,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_246,plain,(
    ! [B_101,A_102] : k2_xboole_0(B_101,A_102) = k2_xboole_0(A_102,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_50])).

tff(c_432,plain,(
    ! [A_127,B_128] :
      ( k4_xboole_0(A_127,B_128) = k3_subset_1(A_127,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_441,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_432])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_454,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_16])).

tff(c_457,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_454])).

tff(c_1200,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_457])).

tff(c_66,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k3_subset_1(A_72,B_73),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_914,plain,(
    ! [A_203,B_204,C_205] :
      ( k4_subset_1(A_203,B_204,C_205) = k2_xboole_0(B_204,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(A_203))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7832,plain,(
    ! [A_510,B_511,B_512] :
      ( k4_subset_1(A_510,B_511,k3_subset_1(A_510,B_512)) = k2_xboole_0(B_511,k3_subset_1(A_510,B_512))
      | ~ m1_subset_1(B_511,k1_zfmisc_1(A_510))
      | ~ m1_subset_1(B_512,k1_zfmisc_1(A_510)) ) ),
    inference(resolution,[status(thm)],[c_66,c_914])).

tff(c_8131,plain,(
    ! [B_515] :
      ( k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6',B_515)) = k2_xboole_0('#skF_7',k3_subset_1('#skF_6',B_515))
      | ~ m1_subset_1(B_515,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_74,c_7832])).

tff(c_8182,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_8131])).

tff(c_8214,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_8182])).

tff(c_8216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_8214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.45/2.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.45/2.91  
% 8.45/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.45/2.92  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 8.45/2.92  
% 8.45/2.92  %Foreground sorts:
% 8.45/2.92  
% 8.45/2.92  
% 8.45/2.92  %Background operators:
% 8.45/2.92  
% 8.45/2.92  
% 8.45/2.92  %Foreground operators:
% 8.45/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.45/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.45/2.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.45/2.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.45/2.92  tff('#skF_7', type, '#skF_7': $i).
% 8.45/2.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.45/2.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.45/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.45/2.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.45/2.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.45/2.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.45/2.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.45/2.92  tff('#skF_6', type, '#skF_6': $i).
% 8.45/2.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.45/2.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.45/2.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.45/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.45/2.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.45/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.45/2.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.45/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.45/2.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.45/2.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.45/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.45/2.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.45/2.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.45/2.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.45/2.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.45/2.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.45/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.45/2.92  
% 8.45/2.93  tff(f_87, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.45/2.93  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 8.45/2.93  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.45/2.93  tff(f_72, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 8.45/2.93  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.45/2.93  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.45/2.93  tff(f_68, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 8.45/2.93  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.45/2.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.45/2.93  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.45/2.93  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.45/2.93  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.45/2.93  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.45/2.93  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.45/2.93  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.45/2.93  tff(f_104, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.45/2.93  tff(c_62, plain, (![A_69]: (k2_subset_1(A_69)=A_69)), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.45/2.93  tff(c_72, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.45/2.93  tff(c_75, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_72])).
% 8.45/2.93  tff(c_74, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.45/2.93  tff(c_68, plain, (![A_74]: (~v1_xboole_0(k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.45/2.93  tff(c_52, plain, (![A_66]: (k3_tarski(k1_zfmisc_1(A_66))=A_66)), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.45/2.93  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.45/2.93  tff(c_56, plain, (![B_68, A_67]: (r2_hidden(B_68, A_67) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.45/2.93  tff(c_463, plain, (![C_131, A_132, D_133]: (r2_hidden(C_131, k3_tarski(A_132)) | ~r2_hidden(D_133, A_132) | ~r2_hidden(C_131, D_133))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.45/2.93  tff(c_618, plain, (![C_165, A_166, B_167]: (r2_hidden(C_165, k3_tarski(A_166)) | ~r2_hidden(C_165, B_167) | ~m1_subset_1(B_167, A_166) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_56, c_463])).
% 8.45/2.93  tff(c_1051, plain, (![A_217, B_218, A_219]: (r2_hidden('#skF_1'(A_217, B_218), k3_tarski(A_219)) | ~m1_subset_1(A_217, A_219) | v1_xboole_0(A_219) | r1_tarski(A_217, B_218))), inference(resolution, [status(thm)], [c_8, c_618])).
% 8.45/2.93  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.45/2.93  tff(c_1089, plain, (![A_223, A_224]: (~m1_subset_1(A_223, A_224) | v1_xboole_0(A_224) | r1_tarski(A_223, k3_tarski(A_224)))), inference(resolution, [status(thm)], [c_1051, c_6])).
% 8.45/2.93  tff(c_1113, plain, (![A_223, A_66]: (~m1_subset_1(A_223, k1_zfmisc_1(A_66)) | v1_xboole_0(k1_zfmisc_1(A_66)) | r1_tarski(A_223, A_66))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1089])).
% 8.45/2.93  tff(c_1120, plain, (![A_225, A_226]: (~m1_subset_1(A_225, k1_zfmisc_1(A_226)) | r1_tarski(A_225, A_226))), inference(negUnitSimplification, [status(thm)], [c_68, c_1113])).
% 8.45/2.93  tff(c_1158, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_1120])).
% 8.45/2.93  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.45/2.93  tff(c_1169, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_1158, c_14])).
% 8.45/2.93  tff(c_104, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.45/2.93  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.45/2.93  tff(c_119, plain, (![A_84, B_83]: (k2_xboole_0(A_84, k3_xboole_0(B_83, A_84))=A_84)), inference(superposition, [status(thm), theory('equality')], [c_104, c_12])).
% 8.45/2.93  tff(c_1179, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1169, c_119])).
% 8.45/2.93  tff(c_18, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.45/2.93  tff(c_204, plain, (![A_89, B_90]: (k3_tarski(k2_tarski(A_89, B_90))=k2_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.45/2.93  tff(c_240, plain, (![B_101, A_102]: (k3_tarski(k2_tarski(B_101, A_102))=k2_xboole_0(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_18, c_204])).
% 8.45/2.93  tff(c_50, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.45/2.93  tff(c_246, plain, (![B_101, A_102]: (k2_xboole_0(B_101, A_102)=k2_xboole_0(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_240, c_50])).
% 8.45/2.93  tff(c_432, plain, (![A_127, B_128]: (k4_xboole_0(A_127, B_128)=k3_subset_1(A_127, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.45/2.93  tff(c_441, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_432])).
% 8.45/2.93  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.45/2.93  tff(c_454, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_441, c_16])).
% 8.45/2.93  tff(c_457, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_454])).
% 8.45/2.93  tff(c_1200, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_457])).
% 8.45/2.93  tff(c_66, plain, (![A_72, B_73]: (m1_subset_1(k3_subset_1(A_72, B_73), k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.45/2.93  tff(c_914, plain, (![A_203, B_204, C_205]: (k4_subset_1(A_203, B_204, C_205)=k2_xboole_0(B_204, C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(A_203)) | ~m1_subset_1(B_204, k1_zfmisc_1(A_203)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.45/2.93  tff(c_7832, plain, (![A_510, B_511, B_512]: (k4_subset_1(A_510, B_511, k3_subset_1(A_510, B_512))=k2_xboole_0(B_511, k3_subset_1(A_510, B_512)) | ~m1_subset_1(B_511, k1_zfmisc_1(A_510)) | ~m1_subset_1(B_512, k1_zfmisc_1(A_510)))), inference(resolution, [status(thm)], [c_66, c_914])).
% 8.45/2.93  tff(c_8131, plain, (![B_515]: (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', B_515))=k2_xboole_0('#skF_7', k3_subset_1('#skF_6', B_515)) | ~m1_subset_1(B_515, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_74, c_7832])).
% 8.45/2.93  tff(c_8182, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_8131])).
% 8.45/2.93  tff(c_8214, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_8182])).
% 8.45/2.93  tff(c_8216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_8214])).
% 8.45/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.45/2.93  
% 8.45/2.93  Inference rules
% 8.45/2.93  ----------------------
% 8.45/2.93  #Ref     : 0
% 8.45/2.93  #Sup     : 1862
% 8.45/2.93  #Fact    : 0
% 8.45/2.93  #Define  : 0
% 8.45/2.93  #Split   : 9
% 8.45/2.93  #Chain   : 0
% 8.45/2.93  #Close   : 0
% 8.45/2.93  
% 8.45/2.93  Ordering : KBO
% 8.45/2.93  
% 8.45/2.93  Simplification rules
% 8.45/2.93  ----------------------
% 8.45/2.93  #Subsume      : 220
% 8.45/2.93  #Demod        : 648
% 8.45/2.93  #Tautology    : 342
% 8.45/2.93  #SimpNegUnit  : 255
% 8.45/2.93  #BackRed      : 90
% 8.45/2.93  
% 8.45/2.93  #Partial instantiations: 0
% 8.45/2.93  #Strategies tried      : 1
% 8.45/2.93  
% 8.45/2.93  Timing (in seconds)
% 8.45/2.93  ----------------------
% 8.45/2.94  Preprocessing        : 0.39
% 8.45/2.94  Parsing              : 0.19
% 8.45/2.94  CNF conversion       : 0.03
% 8.45/2.94  Main loop            : 1.73
% 8.45/2.94  Inferencing          : 0.49
% 8.45/2.94  Reduction            : 0.57
% 8.45/2.94  Demodulation         : 0.41
% 8.45/2.94  BG Simplification    : 0.07
% 8.45/2.94  Subsumption          : 0.47
% 8.45/2.94  Abstraction          : 0.10
% 8.45/2.94  MUC search           : 0.00
% 8.45/2.94  Cooper               : 0.00
% 8.45/2.94  Total                : 2.16
% 8.45/2.94  Index Insertion      : 0.00
% 8.45/2.94  Index Deletion       : 0.00
% 8.45/2.94  Index Matching       : 0.00
% 8.45/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
