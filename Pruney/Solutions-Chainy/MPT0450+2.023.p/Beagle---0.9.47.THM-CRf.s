%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 263 expanded)
%              Number of leaves         :   24 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 394 expanded)
%              Number of equality atoms :    8 ( 128 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(B_45,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_18,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k3_xboole_0(A_30,B_31))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(k3_xboole_0(B_46,A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_18])).

tff(c_20,plain,(
    ! [A_32,B_34] :
      ( r1_tarski(k3_relat_1(A_32),k3_relat_1(B_34))
      | ~ r1_tarski(A_32,B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_170,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [B_45,A_44] : k3_xboole_0(B_45,A_44) = k3_xboole_0(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_22,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_147,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_3')),k3_xboole_0(k3_relat_1('#skF_4'),k3_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_22])).

tff(c_188,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_3')),k3_relat_1('#skF_3'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_3')),k3_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_170,c_147])).

tff(c_191,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_3')),k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_194,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_191])).

tff(c_197,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_198,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_201,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_198])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_201])).

tff(c_210,plain,(
    v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_211,plain,(
    ! [A_63,B_64] :
      ( r2_hidden(k4_tarski('#skF_1'(A_63,B_64),'#skF_2'(A_63,B_64)),A_63)
      | r1_tarski(A_63,B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_13,B_23] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_13,B_23),'#skF_2'(A_13,B_23)),B_23)
      | r1_tarski(A_13,B_23)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_217,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_211,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_228,plain,(
    ! [B_66,C_67] :
      ( r1_tarski(k3_xboole_0(B_66,C_67),B_66)
      | ~ v1_relat_1(k3_xboole_0(B_66,C_67)) ) ),
    inference(resolution,[status(thm)],[c_217,c_2])).

tff(c_209,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_231,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_228,c_209])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_231])).

tff(c_250,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_3')),k3_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_254,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_250])).

tff(c_257,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_254])).

tff(c_258,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_261,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_258])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_261])).

tff(c_270,plain,(
    v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_271,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(k4_tarski('#skF_1'(A_68,B_69),'#skF_2'(A_68,B_69)),A_68)
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_281,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_271,c_14])).

tff(c_292,plain,(
    ! [B_75,C_76] :
      ( r1_tarski(k3_xboole_0(B_75,C_76),B_75)
      | ~ v1_relat_1(k3_xboole_0(B_75,C_76)) ) ),
    inference(resolution,[status(thm)],[c_281,c_2])).

tff(c_309,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k3_xboole_0(B_77,A_78),A_78)
      | ~ v1_relat_1(k3_xboole_0(A_78,B_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_292])).

tff(c_269,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_312,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_309,c_269])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_91,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.06/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.28  
% 2.24/1.30  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.24/1.30  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.24/1.30  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.24/1.30  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.24/1.30  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.24/1.30  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.24/1.30  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 2.24/1.30  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.24/1.30  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.30  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.30  tff(c_61, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.30  tff(c_85, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(B_45, A_44))), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 2.24/1.30  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.30  tff(c_108, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 2.24/1.30  tff(c_18, plain, (![A_30, B_31]: (v1_relat_1(k3_xboole_0(A_30, B_31)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.30  tff(c_123, plain, (![B_46, A_47]: (v1_relat_1(k3_xboole_0(B_46, A_47)) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_108, c_18])).
% 2.24/1.30  tff(c_20, plain, (![A_32, B_34]: (r1_tarski(k3_relat_1(A_32), k3_relat_1(B_34)) | ~r1_tarski(A_32, B_34) | ~v1_relat_1(B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.24/1.30  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.30  tff(c_170, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.30  tff(c_91, plain, (![B_45, A_44]: (k3_xboole_0(B_45, A_44)=k3_xboole_0(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 2.24/1.30  tff(c_22, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.30  tff(c_147, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k3_xboole_0(k3_relat_1('#skF_4'), k3_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_22])).
% 2.24/1.30  tff(c_188, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k3_relat_1('#skF_3')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k3_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_170, c_147])).
% 2.24/1.30  tff(c_191, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_188])).
% 2.24/1.30  tff(c_194, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_191])).
% 2.24/1.30  tff(c_197, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 2.24/1.30  tff(c_198, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_197])).
% 2.24/1.30  tff(c_201, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_198])).
% 2.24/1.30  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_201])).
% 2.24/1.30  tff(c_210, plain, (v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_197])).
% 2.24/1.30  tff(c_211, plain, (![A_63, B_64]: (r2_hidden(k4_tarski('#skF_1'(A_63, B_64), '#skF_2'(A_63, B_64)), A_63) | r1_tarski(A_63, B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.30  tff(c_14, plain, (![A_13, B_23]: (~r2_hidden(k4_tarski('#skF_1'(A_13, B_23), '#skF_2'(A_13, B_23)), B_23) | r1_tarski(A_13, B_23) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.30  tff(c_217, plain, (![A_65]: (r1_tarski(A_65, A_65) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_211, c_14])).
% 2.24/1.30  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.30  tff(c_228, plain, (![B_66, C_67]: (r1_tarski(k3_xboole_0(B_66, C_67), B_66) | ~v1_relat_1(k3_xboole_0(B_66, C_67)))), inference(resolution, [status(thm)], [c_217, c_2])).
% 2.24/1.30  tff(c_209, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_197])).
% 2.24/1.30  tff(c_231, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_228, c_209])).
% 2.24/1.30  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_231])).
% 2.24/1.30  tff(c_250, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k3_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_188])).
% 2.24/1.30  tff(c_254, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_250])).
% 2.24/1.30  tff(c_257, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_254])).
% 2.24/1.30  tff(c_258, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_257])).
% 2.24/1.30  tff(c_261, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_258])).
% 2.24/1.30  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_261])).
% 2.24/1.30  tff(c_270, plain, (v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_257])).
% 2.24/1.30  tff(c_271, plain, (![A_68, B_69]: (r2_hidden(k4_tarski('#skF_1'(A_68, B_69), '#skF_2'(A_68, B_69)), A_68) | r1_tarski(A_68, B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.30  tff(c_281, plain, (![A_74]: (r1_tarski(A_74, A_74) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_271, c_14])).
% 2.24/1.30  tff(c_292, plain, (![B_75, C_76]: (r1_tarski(k3_xboole_0(B_75, C_76), B_75) | ~v1_relat_1(k3_xboole_0(B_75, C_76)))), inference(resolution, [status(thm)], [c_281, c_2])).
% 2.24/1.30  tff(c_309, plain, (![B_77, A_78]: (r1_tarski(k3_xboole_0(B_77, A_78), A_78) | ~v1_relat_1(k3_xboole_0(A_78, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_292])).
% 2.24/1.30  tff(c_269, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_257])).
% 2.24/1.30  tff(c_312, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_309, c_269])).
% 2.24/1.30  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_91, c_312])).
% 2.24/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  Inference rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Ref     : 0
% 2.24/1.30  #Sup     : 68
% 2.24/1.30  #Fact    : 0
% 2.24/1.30  #Define  : 0
% 2.24/1.30  #Split   : 3
% 2.24/1.30  #Chain   : 0
% 2.24/1.30  #Close   : 0
% 2.24/1.30  
% 2.24/1.30  Ordering : KBO
% 2.24/1.30  
% 2.24/1.30  Simplification rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Subsume      : 9
% 2.24/1.30  #Demod        : 12
% 2.24/1.30  #Tautology    : 27
% 2.24/1.30  #SimpNegUnit  : 0
% 2.24/1.30  #BackRed      : 0
% 2.24/1.30  
% 2.24/1.30  #Partial instantiations: 0
% 2.24/1.30  #Strategies tried      : 1
% 2.24/1.30  
% 2.24/1.30  Timing (in seconds)
% 2.24/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.30
% 2.24/1.30  Parsing              : 0.16
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.22
% 2.24/1.30  Inferencing          : 0.09
% 2.24/1.30  Reduction            : 0.07
% 2.24/1.30  Demodulation         : 0.05
% 2.24/1.30  BG Simplification    : 0.01
% 2.24/1.30  Subsumption          : 0.04
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.56
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
