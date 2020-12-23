%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   59 (  63 expanded)
%              Number of leaves         :   38 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_60,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_74,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_92,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_98,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_26,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_376,plain,(
    ! [A_126,B_127] : k1_setfam_1(k2_tarski(A_126,B_127)) = k3_xboole_0(A_126,B_127) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_406,plain,(
    ! [A_130,B_131] : k1_setfam_1(k2_tarski(A_130,B_131)) = k3_xboole_0(B_131,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_376])).

tff(c_40,plain,(
    ! [A_50,B_51] : k1_setfam_1(k2_tarski(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_412,plain,(
    ! [B_131,A_130] : k3_xboole_0(B_131,A_130) = k3_xboole_0(A_130,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_40])).

tff(c_94,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k3_xboole_0(B_18,C_19))
      | ~ r1_tarski(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1830,plain,(
    ! [B_207,A_208] :
      ( B_207 = A_208
      | ~ r1_tarski(B_207,A_208)
      | ~ r1_tarski(A_208,B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7652,plain,(
    ! [A_340,B_341] :
      ( k3_xboole_0(A_340,B_341) = A_340
      | ~ r1_tarski(A_340,k3_xboole_0(A_340,B_341)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1830])).

tff(c_7659,plain,(
    ! [B_18,C_19] :
      ( k3_xboole_0(B_18,C_19) = B_18
      | ~ r1_tarski(B_18,C_19)
      | ~ r1_tarski(B_18,B_18) ) ),
    inference(resolution,[status(thm)],[c_22,c_7652])).

tff(c_7699,plain,(
    ! [B_342,C_343] :
      ( k3_xboole_0(B_342,C_343) = B_342
      | ~ r1_tarski(B_342,C_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7659])).

tff(c_7836,plain,(
    k3_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_7699])).

tff(c_8800,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_7836])).

tff(c_76,plain,(
    ! [A_84,C_86,B_85] :
      ( k3_xboole_0(A_84,k10_relat_1(C_86,B_85)) = k10_relat_1(k7_relat_1(C_86,A_84),B_85)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10042,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8800,c_76])).

tff(c_10129,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_10042])).

tff(c_10131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_10129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:05:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.41  
% 6.64/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.41  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.64/2.41  
% 6.64/2.41  %Foreground sorts:
% 6.64/2.41  
% 6.64/2.41  
% 6.64/2.41  %Background operators:
% 6.64/2.41  
% 6.64/2.41  
% 6.64/2.41  %Foreground operators:
% 6.64/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.64/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.64/2.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.64/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.64/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.64/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.64/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.64/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.64/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.64/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.64/2.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.64/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.64/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.64/2.41  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.64/2.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.64/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.64/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.64/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.64/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.64/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.64/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.64/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.64/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.64/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.64/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.64/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.64/2.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.64/2.41  
% 6.64/2.42  tff(f_177, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 6.64/2.42  tff(f_60, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.64/2.42  tff(f_74, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.64/2.42  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.64/2.42  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.64/2.42  tff(f_50, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.64/2.42  tff(f_132, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 6.64/2.42  tff(c_92, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.64/2.42  tff(c_98, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.64/2.42  tff(c_26, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.64/2.42  tff(c_376, plain, (![A_126, B_127]: (k1_setfam_1(k2_tarski(A_126, B_127))=k3_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.64/2.42  tff(c_406, plain, (![A_130, B_131]: (k1_setfam_1(k2_tarski(A_130, B_131))=k3_xboole_0(B_131, A_130))), inference(superposition, [status(thm), theory('equality')], [c_26, c_376])).
% 6.64/2.42  tff(c_40, plain, (![A_50, B_51]: (k1_setfam_1(k2_tarski(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.64/2.42  tff(c_412, plain, (![B_131, A_130]: (k3_xboole_0(B_131, A_130)=k3_xboole_0(A_130, B_131))), inference(superposition, [status(thm), theory('equality')], [c_406, c_40])).
% 6.64/2.42  tff(c_94, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.64/2.42  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.64/2.42  tff(c_22, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k3_xboole_0(B_18, C_19)) | ~r1_tarski(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.64/2.42  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.64/2.42  tff(c_1830, plain, (![B_207, A_208]: (B_207=A_208 | ~r1_tarski(B_207, A_208) | ~r1_tarski(A_208, B_207))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.64/2.42  tff(c_7652, plain, (![A_340, B_341]: (k3_xboole_0(A_340, B_341)=A_340 | ~r1_tarski(A_340, k3_xboole_0(A_340, B_341)))), inference(resolution, [status(thm)], [c_20, c_1830])).
% 6.64/2.42  tff(c_7659, plain, (![B_18, C_19]: (k3_xboole_0(B_18, C_19)=B_18 | ~r1_tarski(B_18, C_19) | ~r1_tarski(B_18, B_18))), inference(resolution, [status(thm)], [c_22, c_7652])).
% 6.64/2.42  tff(c_7699, plain, (![B_342, C_343]: (k3_xboole_0(B_342, C_343)=B_342 | ~r1_tarski(B_342, C_343))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7659])).
% 6.64/2.42  tff(c_7836, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_7699])).
% 6.64/2.42  tff(c_8800, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_412, c_7836])).
% 6.64/2.42  tff(c_76, plain, (![A_84, C_86, B_85]: (k3_xboole_0(A_84, k10_relat_1(C_86, B_85))=k10_relat_1(k7_relat_1(C_86, A_84), B_85) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.64/2.42  tff(c_10042, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8800, c_76])).
% 6.64/2.42  tff(c_10129, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_10042])).
% 6.64/2.42  tff(c_10131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_10129])).
% 6.64/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.42  
% 6.64/2.42  Inference rules
% 6.64/2.42  ----------------------
% 6.64/2.42  #Ref     : 0
% 6.64/2.42  #Sup     : 2437
% 6.64/2.42  #Fact    : 0
% 6.64/2.42  #Define  : 0
% 6.64/2.42  #Split   : 6
% 6.64/2.42  #Chain   : 0
% 6.64/2.42  #Close   : 0
% 6.64/2.42  
% 6.64/2.42  Ordering : KBO
% 6.64/2.42  
% 6.64/2.42  Simplification rules
% 6.64/2.42  ----------------------
% 6.64/2.42  #Subsume      : 115
% 6.64/2.42  #Demod        : 2083
% 6.64/2.42  #Tautology    : 1735
% 6.64/2.42  #SimpNegUnit  : 1
% 6.64/2.42  #BackRed      : 0
% 6.64/2.42  
% 6.64/2.43  #Partial instantiations: 0
% 6.64/2.43  #Strategies tried      : 1
% 6.64/2.43  
% 6.64/2.43  Timing (in seconds)
% 6.64/2.43  ----------------------
% 6.79/2.43  Preprocessing        : 0.38
% 6.79/2.43  Parsing              : 0.20
% 6.79/2.43  CNF conversion       : 0.03
% 6.79/2.43  Main loop            : 1.28
% 6.79/2.43  Inferencing          : 0.34
% 6.79/2.43  Reduction            : 0.62
% 6.79/2.43  Demodulation         : 0.52
% 6.79/2.43  BG Simplification    : 0.05
% 6.79/2.43  Subsumption          : 0.20
% 6.79/2.43  Abstraction          : 0.06
% 6.79/2.43  MUC search           : 0.00
% 6.79/2.43  Cooper               : 0.00
% 6.79/2.43  Total                : 1.69
% 6.79/2.43  Index Insertion      : 0.00
% 6.79/2.43  Index Deletion       : 0.00
% 6.79/2.43  Index Matching       : 0.00
% 6.79/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
