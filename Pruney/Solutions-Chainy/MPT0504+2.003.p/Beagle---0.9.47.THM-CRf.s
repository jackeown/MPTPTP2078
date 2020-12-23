%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :   50 (  69 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 121 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [B_33,A_34] :
      ( k7_relat_1(B_33,A_34) = B_33
      | ~ r1_tarski(k1_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_483,plain,(
    ! [B_55,A_56] :
      ( k7_relat_1(k7_relat_1(B_55,A_56),A_56) = k7_relat_1(B_55,A_56)
      | ~ v1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_12,c_108])).

tff(c_486,plain,(
    ! [A_10,B_11] :
      ( k7_relat_1(k7_relat_1(A_10,B_11),B_11) = k7_relat_1(A_10,B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_483])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_25)),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [B_24,A_25] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_24,A_25)),A_25) = k1_relat_1(k7_relat_1(B_24,A_25))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_158,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,k1_relat_1(k7_relat_1(B_39,A_38))) = k1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_474,plain,(
    ! [B_52,A_53,B_54] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_52,A_53)),B_54)
      | ~ r1_tarski(A_53,B_54)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_2847,plain,(
    ! [B_147,A_148,B_149] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_147,A_148)),B_149) = k1_relat_1(k7_relat_1(B_147,A_148))
      | ~ r1_tarski(A_148,B_149)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_474,c_6])).

tff(c_79,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(k3_xboole_0(A_26,C_27),B_28)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_35,C_36,B_37] :
      ( k3_xboole_0(k3_xboole_0(A_35,C_36),B_37) = k3_xboole_0(A_35,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(resolution,[status(thm)],[c_79,c_6])).

tff(c_88,plain,(
    ! [B_2,A_1,B_28] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_28)
      | ~ r1_tarski(A_1,B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_516,plain,(
    ! [A_59,C_60,B_61,B_62] :
      ( r1_tarski(k3_xboole_0(A_59,C_60),B_61)
      | ~ r1_tarski(B_62,B_61)
      | ~ r1_tarski(A_59,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_88])).

tff(c_531,plain,(
    ! [A_59,C_60] :
      ( r1_tarski(k3_xboole_0(A_59,C_60),'#skF_2')
      | ~ r1_tarski(A_59,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_516])).

tff(c_5554,plain,(
    ! [B_238,A_239,B_240] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_238,A_239)),'#skF_2')
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_238,A_239)),'#skF_1')
      | ~ r1_tarski(A_239,B_240)
      | ~ v1_relat_1(B_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2847,c_531])).

tff(c_5923,plain,(
    ! [B_249] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_249,'#skF_1')),'#skF_2')
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_249,'#skF_1')),'#skF_1')
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_18,c_5554])).

tff(c_10789,plain,(
    ! [A_324] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_324,'#skF_1')),'#skF_2')
      | ~ r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(A_324,'#skF_1'),'#skF_1')),'#skF_1')
      | ~ v1_relat_1(k7_relat_1(A_324,'#skF_1'))
      | ~ v1_relat_1(A_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_5923])).

tff(c_10810,plain,(
    ! [A_325] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_325,'#skF_1')),'#skF_2')
      | ~ v1_relat_1(A_325)
      | ~ v1_relat_1(k7_relat_1(A_325,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_10789])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11137,plain,(
    ! [A_332] :
      ( k7_relat_1(k7_relat_1(A_332,'#skF_1'),'#skF_2') = k7_relat_1(A_332,'#skF_1')
      | ~ v1_relat_1(A_332)
      | ~ v1_relat_1(k7_relat_1(A_332,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10810,c_14])).

tff(c_11147,plain,(
    ! [A_333] :
      ( k7_relat_1(k7_relat_1(A_333,'#skF_1'),'#skF_2') = k7_relat_1(A_333,'#skF_1')
      | ~ v1_relat_1(A_333) ) ),
    inference(resolution,[status(thm)],[c_10,c_11137])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11192,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11147,c_16])).

tff(c_11211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/3.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.51  
% 10.01/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.51  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 10.01/3.51  
% 10.01/3.51  %Foreground sorts:
% 10.01/3.51  
% 10.01/3.51  
% 10.01/3.51  %Background operators:
% 10.01/3.51  
% 10.01/3.51  
% 10.01/3.51  %Foreground operators:
% 10.01/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/3.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.01/3.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.01/3.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.01/3.51  tff('#skF_2', type, '#skF_2': $i).
% 10.01/3.51  tff('#skF_3', type, '#skF_3': $i).
% 10.01/3.51  tff('#skF_1', type, '#skF_1': $i).
% 10.01/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/3.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.01/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/3.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.01/3.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.01/3.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.01/3.51  
% 10.01/3.52  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 10.01/3.52  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 10.01/3.52  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 10.01/3.52  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 10.01/3.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.01/3.52  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.01/3.52  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 10.01/3.52  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.52  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.52  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/3.52  tff(c_108, plain, (![B_33, A_34]: (k7_relat_1(B_33, A_34)=B_33 | ~r1_tarski(k1_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.52  tff(c_483, plain, (![B_55, A_56]: (k7_relat_1(k7_relat_1(B_55, A_56), A_56)=k7_relat_1(B_55, A_56) | ~v1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_12, c_108])).
% 10.01/3.52  tff(c_486, plain, (![A_10, B_11]: (k7_relat_1(k7_relat_1(A_10, B_11), B_11)=k7_relat_1(A_10, B_11) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_10, c_483])).
% 10.01/3.52  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.01/3.52  tff(c_73, plain, (![B_24, A_25]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_25)), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/3.52  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.01/3.52  tff(c_76, plain, (![B_24, A_25]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_24, A_25)), A_25)=k1_relat_1(k7_relat_1(B_24, A_25)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_73, c_6])).
% 10.01/3.52  tff(c_158, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k1_relat_1(k7_relat_1(B_39, A_38)))=k1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76])).
% 10.01/3.52  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/3.52  tff(c_474, plain, (![B_52, A_53, B_54]: (r1_tarski(k1_relat_1(k7_relat_1(B_52, A_53)), B_54) | ~r1_tarski(A_53, B_54) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 10.01/3.52  tff(c_2847, plain, (![B_147, A_148, B_149]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_147, A_148)), B_149)=k1_relat_1(k7_relat_1(B_147, A_148)) | ~r1_tarski(A_148, B_149) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_474, c_6])).
% 10.01/3.52  tff(c_79, plain, (![A_26, C_27, B_28]: (r1_tarski(k3_xboole_0(A_26, C_27), B_28) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/3.52  tff(c_113, plain, (![A_35, C_36, B_37]: (k3_xboole_0(k3_xboole_0(A_35, C_36), B_37)=k3_xboole_0(A_35, C_36) | ~r1_tarski(A_35, B_37))), inference(resolution, [status(thm)], [c_79, c_6])).
% 10.01/3.52  tff(c_88, plain, (![B_2, A_1, B_28]: (r1_tarski(k3_xboole_0(B_2, A_1), B_28) | ~r1_tarski(A_1, B_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 10.01/3.52  tff(c_516, plain, (![A_59, C_60, B_61, B_62]: (r1_tarski(k3_xboole_0(A_59, C_60), B_61) | ~r1_tarski(B_62, B_61) | ~r1_tarski(A_59, B_62))), inference(superposition, [status(thm), theory('equality')], [c_113, c_88])).
% 10.01/3.52  tff(c_531, plain, (![A_59, C_60]: (r1_tarski(k3_xboole_0(A_59, C_60), '#skF_2') | ~r1_tarski(A_59, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_516])).
% 10.01/3.52  tff(c_5554, plain, (![B_238, A_239, B_240]: (r1_tarski(k1_relat_1(k7_relat_1(B_238, A_239)), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1(B_238, A_239)), '#skF_1') | ~r1_tarski(A_239, B_240) | ~v1_relat_1(B_238))), inference(superposition, [status(thm), theory('equality')], [c_2847, c_531])).
% 10.01/3.52  tff(c_5923, plain, (![B_249]: (r1_tarski(k1_relat_1(k7_relat_1(B_249, '#skF_1')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1(B_249, '#skF_1')), '#skF_1') | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_18, c_5554])).
% 10.01/3.52  tff(c_10789, plain, (![A_324]: (r1_tarski(k1_relat_1(k7_relat_1(A_324, '#skF_1')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(A_324, '#skF_1'), '#skF_1')), '#skF_1') | ~v1_relat_1(k7_relat_1(A_324, '#skF_1')) | ~v1_relat_1(A_324))), inference(superposition, [status(thm), theory('equality')], [c_486, c_5923])).
% 10.01/3.52  tff(c_10810, plain, (![A_325]: (r1_tarski(k1_relat_1(k7_relat_1(A_325, '#skF_1')), '#skF_2') | ~v1_relat_1(A_325) | ~v1_relat_1(k7_relat_1(A_325, '#skF_1')))), inference(resolution, [status(thm)], [c_12, c_10789])).
% 10.01/3.52  tff(c_14, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.52  tff(c_11137, plain, (![A_332]: (k7_relat_1(k7_relat_1(A_332, '#skF_1'), '#skF_2')=k7_relat_1(A_332, '#skF_1') | ~v1_relat_1(A_332) | ~v1_relat_1(k7_relat_1(A_332, '#skF_1')))), inference(resolution, [status(thm)], [c_10810, c_14])).
% 10.01/3.52  tff(c_11147, plain, (![A_333]: (k7_relat_1(k7_relat_1(A_333, '#skF_1'), '#skF_2')=k7_relat_1(A_333, '#skF_1') | ~v1_relat_1(A_333))), inference(resolution, [status(thm)], [c_10, c_11137])).
% 10.01/3.52  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.52  tff(c_11192, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11147, c_16])).
% 10.01/3.52  tff(c_11211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_11192])).
% 10.01/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.52  
% 10.01/3.52  Inference rules
% 10.01/3.52  ----------------------
% 10.01/3.52  #Ref     : 0
% 10.01/3.52  #Sup     : 3418
% 10.01/3.52  #Fact    : 0
% 10.01/3.52  #Define  : 0
% 10.01/3.52  #Split   : 1
% 10.01/3.52  #Chain   : 0
% 10.01/3.52  #Close   : 0
% 10.01/3.52  
% 10.01/3.52  Ordering : KBO
% 10.01/3.52  
% 10.01/3.52  Simplification rules
% 10.01/3.52  ----------------------
% 10.01/3.52  #Subsume      : 1122
% 10.01/3.52  #Demod        : 515
% 10.01/3.52  #Tautology    : 218
% 10.01/3.52  #SimpNegUnit  : 0
% 10.01/3.52  #BackRed      : 0
% 10.01/3.52  
% 10.01/3.52  #Partial instantiations: 0
% 10.01/3.52  #Strategies tried      : 1
% 10.01/3.52  
% 10.01/3.52  Timing (in seconds)
% 10.01/3.52  ----------------------
% 10.01/3.53  Preprocessing        : 0.30
% 10.01/3.53  Parsing              : 0.17
% 10.01/3.53  CNF conversion       : 0.02
% 10.01/3.53  Main loop            : 2.40
% 10.01/3.53  Inferencing          : 0.56
% 10.01/3.53  Reduction            : 0.67
% 10.01/3.53  Demodulation         : 0.53
% 10.01/3.53  BG Simplification    : 0.09
% 10.01/3.53  Subsumption          : 0.95
% 10.01/3.53  Abstraction          : 0.10
% 10.01/3.53  MUC search           : 0.00
% 10.01/3.53  Cooper               : 0.00
% 10.01/3.53  Total                : 2.72
% 10.01/3.53  Index Insertion      : 0.00
% 10.01/3.53  Index Deletion       : 0.00
% 10.01/3.53  Index Matching       : 0.00
% 10.01/3.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
