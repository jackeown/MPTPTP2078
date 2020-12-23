%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 122 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 ( 170 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_237,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_241,plain,(
    ! [B_53,A_21] :
      ( r1_tarski(B_53,A_21)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_237,c_28])).

tff(c_245,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_241])).

tff(c_257,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_245])).

tff(c_22,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_125,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [A_51] : k3_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [A_51] : k3_xboole_0(A_51,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_2])).

tff(c_580,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_601,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = k4_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_580])).

tff(c_616,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_601])).

tff(c_263,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_281,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_263])).

tff(c_284,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_281])).

tff(c_54,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_139,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_125])).

tff(c_24,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1154,plain,(
    ! [A_106,B_107] :
      ( k4_xboole_0(A_106,B_107) = k3_subset_1(A_106,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1170,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1154])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_526,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_xboole_0(A_68,C_69)
      | ~ r1_tarski(A_68,k4_xboole_0(B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_561,plain,(
    ! [B_70,C_69,B_14] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_70,C_69),B_14),C_69) ),
    inference(resolution,[status(thm)],[c_20,c_526])).

tff(c_1731,plain,(
    ! [B_126] : r1_xboole_0(k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),B_126),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_561])).

tff(c_1756,plain,(
    ! [B_129] : r1_xboole_0(k3_xboole_0(k3_subset_1('#skF_3','#skF_5'),B_129),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1731])).

tff(c_2701,plain,(
    ! [B_165] : r1_xboole_0(k3_xboole_0(B_165,k3_subset_1('#skF_3','#skF_5')),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1756])).

tff(c_2703,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_2701])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k4_xboole_0(B_19,C_20))
      | ~ r1_xboole_0(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_380,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3819,plain,(
    ! [A_185,B_186] :
      ( k4_xboole_0(A_185,B_186) = A_185
      | ~ r1_tarski(A_185,k4_xboole_0(A_185,B_186)) ) ),
    inference(resolution,[status(thm)],[c_20,c_380])).

tff(c_3844,plain,(
    ! [B_19,C_20] :
      ( k4_xboole_0(B_19,C_20) = B_19
      | ~ r1_xboole_0(B_19,C_20)
      | ~ r1_tarski(B_19,B_19) ) ),
    inference(resolution,[status(thm)],[c_26,c_3819])).

tff(c_3899,plain,(
    ! [B_187,C_188] :
      ( k4_xboole_0(B_187,C_188) = B_187
      | ~ r1_xboole_0(B_187,C_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3844])).

tff(c_3978,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2703,c_3899])).

tff(c_4059,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3978,c_24])).

tff(c_4077,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_4059])).

tff(c_610,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_580])).

tff(c_4099,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4077,c_610])).

tff(c_4145,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_4099])).

tff(c_562,plain,(
    ! [B_70,C_69] : r1_xboole_0(k4_xboole_0(B_70,C_69),C_69) ),
    inference(resolution,[status(thm)],[c_8,c_526])).

tff(c_4307,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4145,c_562])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1171,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1154])).

tff(c_1306,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,k4_xboole_0(B_111,C_112))
      | ~ r1_xboole_0(A_110,C_112)
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6415,plain,(
    ! [A_224] :
      ( r1_tarski(A_224,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_224,'#skF_4')
      | ~ r1_tarski(A_224,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_1306])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6433,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6415,c_52])).

tff(c_6442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_4307,c_6433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.21  
% 5.90/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.90/2.21  
% 5.90/2.21  %Foreground sorts:
% 5.90/2.21  
% 5.90/2.21  
% 5.90/2.21  %Background operators:
% 5.90/2.21  
% 5.90/2.21  
% 5.90/2.21  %Foreground operators:
% 5.90/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.90/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.90/2.21  tff('#skF_5', type, '#skF_5': $i).
% 5.90/2.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.90/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.21  tff('#skF_4', type, '#skF_4': $i).
% 5.90/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.90/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.90/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.90/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.21  
% 5.90/2.23  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 5.90/2.23  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.90/2.23  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.90/2.23  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.90/2.23  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.90/2.23  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.90/2.23  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.90/2.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.90/2.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.90/2.23  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.90/2.23  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.90/2.23  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.90/2.23  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.90/2.23  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.90/2.23  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 5.90/2.23  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.90/2.23  tff(c_50, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.90/2.23  tff(c_237, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.90/2.23  tff(c_28, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.90/2.23  tff(c_241, plain, (![B_53, A_21]: (r1_tarski(B_53, A_21) | ~m1_subset_1(B_53, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_237, c_28])).
% 5.90/2.23  tff(c_245, plain, (![B_55, A_56]: (r1_tarski(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)))), inference(negUnitSimplification, [status(thm)], [c_50, c_241])).
% 5.90/2.23  tff(c_257, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_245])).
% 5.90/2.23  tff(c_22, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.90/2.23  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.90/2.23  tff(c_125, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.23  tff(c_156, plain, (![A_51]: (k3_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_125])).
% 5.90/2.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.23  tff(c_165, plain, (![A_51]: (k3_xboole_0(A_51, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_2])).
% 5.90/2.23  tff(c_580, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.90/2.23  tff(c_601, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=k4_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_580])).
% 5.90/2.23  tff(c_616, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_601])).
% 5.90/2.23  tff(c_263, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.23  tff(c_281, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_263])).
% 5.90/2.23  tff(c_284, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_281])).
% 5.90/2.23  tff(c_54, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.90/2.23  tff(c_139, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_54, c_125])).
% 5.90/2.23  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.23  tff(c_1154, plain, (![A_106, B_107]: (k4_xboole_0(A_106, B_107)=k3_subset_1(A_106, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.90/2.23  tff(c_1170, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_1154])).
% 5.90/2.23  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.90/2.23  tff(c_526, plain, (![A_68, C_69, B_70]: (r1_xboole_0(A_68, C_69) | ~r1_tarski(A_68, k4_xboole_0(B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.90/2.23  tff(c_561, plain, (![B_70, C_69, B_14]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_70, C_69), B_14), C_69))), inference(resolution, [status(thm)], [c_20, c_526])).
% 5.90/2.23  tff(c_1731, plain, (![B_126]: (r1_xboole_0(k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), B_126), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_561])).
% 5.90/2.23  tff(c_1756, plain, (![B_129]: (r1_xboole_0(k3_xboole_0(k3_subset_1('#skF_3', '#skF_5'), B_129), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1731])).
% 5.90/2.23  tff(c_2701, plain, (![B_165]: (r1_xboole_0(k3_xboole_0(B_165, k3_subset_1('#skF_3', '#skF_5')), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1756])).
% 5.90/2.23  tff(c_2703, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_139, c_2701])).
% 5.90/2.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.90/2.23  tff(c_26, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k4_xboole_0(B_19, C_20)) | ~r1_xboole_0(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.90/2.23  tff(c_380, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.90/2.23  tff(c_3819, plain, (![A_185, B_186]: (k4_xboole_0(A_185, B_186)=A_185 | ~r1_tarski(A_185, k4_xboole_0(A_185, B_186)))), inference(resolution, [status(thm)], [c_20, c_380])).
% 5.90/2.23  tff(c_3844, plain, (![B_19, C_20]: (k4_xboole_0(B_19, C_20)=B_19 | ~r1_xboole_0(B_19, C_20) | ~r1_tarski(B_19, B_19))), inference(resolution, [status(thm)], [c_26, c_3819])).
% 5.90/2.23  tff(c_3899, plain, (![B_187, C_188]: (k4_xboole_0(B_187, C_188)=B_187 | ~r1_xboole_0(B_187, C_188))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3844])).
% 5.90/2.23  tff(c_3978, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2703, c_3899])).
% 5.90/2.23  tff(c_4059, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3978, c_24])).
% 5.90/2.23  tff(c_4077, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_284, c_4059])).
% 5.90/2.23  tff(c_610, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_580])).
% 5.90/2.23  tff(c_4099, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4077, c_610])).
% 5.90/2.23  tff(c_4145, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_4099])).
% 5.90/2.23  tff(c_562, plain, (![B_70, C_69]: (r1_xboole_0(k4_xboole_0(B_70, C_69), C_69))), inference(resolution, [status(thm)], [c_8, c_526])).
% 5.90/2.23  tff(c_4307, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4145, c_562])).
% 5.90/2.23  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.90/2.23  tff(c_1171, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1154])).
% 5.90/2.23  tff(c_1306, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, k4_xboole_0(B_111, C_112)) | ~r1_xboole_0(A_110, C_112) | ~r1_tarski(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.90/2.23  tff(c_6415, plain, (![A_224]: (r1_tarski(A_224, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_224, '#skF_4') | ~r1_tarski(A_224, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_1306])).
% 5.90/2.23  tff(c_52, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.90/2.23  tff(c_6433, plain, (~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6415, c_52])).
% 5.90/2.23  tff(c_6442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_4307, c_6433])).
% 5.90/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.23  
% 5.90/2.23  Inference rules
% 5.90/2.23  ----------------------
% 5.90/2.23  #Ref     : 0
% 5.90/2.23  #Sup     : 1538
% 5.90/2.23  #Fact    : 0
% 5.90/2.23  #Define  : 0
% 5.90/2.23  #Split   : 3
% 5.90/2.23  #Chain   : 0
% 5.90/2.23  #Close   : 0
% 5.90/2.23  
% 5.90/2.23  Ordering : KBO
% 5.90/2.23  
% 5.90/2.23  Simplification rules
% 5.90/2.23  ----------------------
% 5.90/2.23  #Subsume      : 55
% 5.90/2.23  #Demod        : 1367
% 5.90/2.23  #Tautology    : 1019
% 5.90/2.23  #SimpNegUnit  : 2
% 5.90/2.23  #BackRed      : 2
% 5.90/2.23  
% 5.90/2.23  #Partial instantiations: 0
% 5.90/2.23  #Strategies tried      : 1
% 5.90/2.23  
% 5.90/2.23  Timing (in seconds)
% 5.90/2.23  ----------------------
% 5.90/2.23  Preprocessing        : 0.34
% 5.90/2.23  Parsing              : 0.18
% 5.90/2.23  CNF conversion       : 0.02
% 5.90/2.23  Main loop            : 1.07
% 5.90/2.23  Inferencing          : 0.31
% 5.90/2.23  Reduction            : 0.48
% 5.90/2.23  Demodulation         : 0.39
% 5.90/2.23  BG Simplification    : 0.03
% 5.90/2.23  Subsumption          : 0.18
% 5.90/2.23  Abstraction          : 0.04
% 5.90/2.23  MUC search           : 0.00
% 5.90/2.23  Cooper               : 0.00
% 5.90/2.23  Total                : 1.45
% 5.90/2.23  Index Insertion      : 0.00
% 5.90/2.23  Index Deletion       : 0.00
% 5.90/2.23  Index Matching       : 0.00
% 5.90/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
