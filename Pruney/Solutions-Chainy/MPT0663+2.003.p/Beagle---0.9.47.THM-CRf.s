%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 103 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [B_28,A_29] : k1_setfam_1(k2_tarski(B_28,A_29)) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_14,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_26,plain,(
    r2_hidden('#skF_2',k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_112,plain,(
    r2_hidden('#skF_2',k3_xboole_0('#skF_3',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_26])).

tff(c_171,plain,(
    ! [C_39,B_40,A_41] :
      ( r2_hidden(C_39,B_40)
      | ~ r2_hidden(C_39,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [B_42] :
      ( r2_hidden('#skF_2',B_42)
      | ~ r1_tarski(k3_xboole_0('#skF_3',k1_relat_1('#skF_4')),B_42) ) ),
    inference(resolution,[status(thm)],[c_112,c_171])).

tff(c_194,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_113,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_128,plain,(
    ! [B_30,A_31] : r1_tarski(k3_xboole_0(B_30,A_31),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_193,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_128,c_178])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( r2_hidden(A_14,k1_relat_1(k7_relat_1(C_16,B_15)))
      | ~ r2_hidden(A_14,k1_relat_1(C_16))
      | ~ r2_hidden(A_14,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_375,plain,(
    ! [C_81,B_82,A_83] :
      ( k1_funct_1(k7_relat_1(C_81,B_82),A_83) = k1_funct_1(C_81,A_83)
      | ~ r2_hidden(A_83,k1_relat_1(k7_relat_1(C_81,B_82)))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_920,plain,(
    ! [C_155,B_156,A_157] :
      ( k1_funct_1(k7_relat_1(C_155,B_156),A_157) = k1_funct_1(C_155,A_157)
      | ~ v1_funct_1(C_155)
      | ~ r2_hidden(A_157,k1_relat_1(C_155))
      | ~ r2_hidden(A_157,B_156)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_16,c_375])).

tff(c_962,plain,(
    ! [B_156] :
      ( k1_funct_1(k7_relat_1('#skF_4',B_156),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden('#skF_2',B_156)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_193,c_920])).

tff(c_1023,plain,(
    ! [B_161] :
      ( k1_funct_1(k7_relat_1('#skF_4',B_161),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
      | ~ r2_hidden('#skF_2',B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_962])).

tff(c_24,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1029,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_24])).

tff(c_1037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_1029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.56  
% 3.17/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.56  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.17/1.56  
% 3.17/1.56  %Foreground sorts:
% 3.17/1.56  
% 3.17/1.56  
% 3.17/1.56  %Background operators:
% 3.17/1.56  
% 3.17/1.56  
% 3.17/1.56  %Foreground operators:
% 3.17/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.17/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.17/1.56  
% 3.17/1.57  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.17/1.57  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.17/1.57  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.17/1.57  tff(f_65, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 3.17/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.17/1.57  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.17/1.57  tff(f_56, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 3.17/1.57  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.17/1.57  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.57  tff(c_65, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.57  tff(c_89, plain, (![B_28, A_29]: (k1_setfam_1(k2_tarski(B_28, A_29))=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 3.17/1.57  tff(c_14, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.57  tff(c_95, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_89, c_14])).
% 3.17/1.57  tff(c_26, plain, (r2_hidden('#skF_2', k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.57  tff(c_112, plain, (r2_hidden('#skF_2', k3_xboole_0('#skF_3', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_26])).
% 3.17/1.57  tff(c_171, plain, (![C_39, B_40, A_41]: (r2_hidden(C_39, B_40) | ~r2_hidden(C_39, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.57  tff(c_178, plain, (![B_42]: (r2_hidden('#skF_2', B_42) | ~r1_tarski(k3_xboole_0('#skF_3', k1_relat_1('#skF_4')), B_42))), inference(resolution, [status(thm)], [c_112, c_171])).
% 3.17/1.57  tff(c_194, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_178])).
% 3.17/1.57  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.57  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.57  tff(c_113, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_89, c_14])).
% 3.17/1.57  tff(c_128, plain, (![B_30, A_31]: (r1_tarski(k3_xboole_0(B_30, A_31), A_31))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 3.17/1.57  tff(c_193, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_128, c_178])).
% 3.17/1.57  tff(c_16, plain, (![A_14, C_16, B_15]: (r2_hidden(A_14, k1_relat_1(k7_relat_1(C_16, B_15))) | ~r2_hidden(A_14, k1_relat_1(C_16)) | ~r2_hidden(A_14, B_15) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.57  tff(c_375, plain, (![C_81, B_82, A_83]: (k1_funct_1(k7_relat_1(C_81, B_82), A_83)=k1_funct_1(C_81, A_83) | ~r2_hidden(A_83, k1_relat_1(k7_relat_1(C_81, B_82))) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.57  tff(c_920, plain, (![C_155, B_156, A_157]: (k1_funct_1(k7_relat_1(C_155, B_156), A_157)=k1_funct_1(C_155, A_157) | ~v1_funct_1(C_155) | ~r2_hidden(A_157, k1_relat_1(C_155)) | ~r2_hidden(A_157, B_156) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_16, c_375])).
% 3.17/1.57  tff(c_962, plain, (![B_156]: (k1_funct_1(k7_relat_1('#skF_4', B_156), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~r2_hidden('#skF_2', B_156) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_193, c_920])).
% 3.17/1.57  tff(c_1023, plain, (![B_161]: (k1_funct_1(k7_relat_1('#skF_4', B_161), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_2', B_161))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_962])).
% 3.17/1.57  tff(c_24, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.57  tff(c_1029, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1023, c_24])).
% 3.17/1.57  tff(c_1037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_1029])).
% 3.17/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.57  
% 3.17/1.57  Inference rules
% 3.17/1.57  ----------------------
% 3.17/1.57  #Ref     : 0
% 3.17/1.57  #Sup     : 242
% 3.17/1.57  #Fact    : 0
% 3.17/1.57  #Define  : 0
% 3.17/1.57  #Split   : 0
% 3.17/1.57  #Chain   : 0
% 3.17/1.57  #Close   : 0
% 3.17/1.57  
% 3.17/1.57  Ordering : KBO
% 3.17/1.57  
% 3.17/1.57  Simplification rules
% 3.17/1.57  ----------------------
% 3.17/1.57  #Subsume      : 41
% 3.17/1.57  #Demod        : 30
% 3.17/1.57  #Tautology    : 52
% 3.17/1.57  #SimpNegUnit  : 0
% 3.17/1.57  #BackRed      : 1
% 3.17/1.57  
% 3.17/1.57  #Partial instantiations: 0
% 3.17/1.57  #Strategies tried      : 1
% 3.17/1.57  
% 3.17/1.57  Timing (in seconds)
% 3.17/1.57  ----------------------
% 3.17/1.58  Preprocessing        : 0.36
% 3.17/1.58  Parsing              : 0.17
% 3.17/1.58  CNF conversion       : 0.03
% 3.17/1.58  Main loop            : 0.44
% 3.17/1.58  Inferencing          : 0.15
% 3.17/1.58  Reduction            : 0.14
% 3.17/1.58  Demodulation         : 0.11
% 3.17/1.58  BG Simplification    : 0.03
% 3.17/1.58  Subsumption          : 0.10
% 3.17/1.58  Abstraction          : 0.03
% 3.17/1.58  MUC search           : 0.00
% 3.17/1.58  Cooper               : 0.00
% 3.17/1.58  Total                : 0.83
% 3.17/1.58  Index Insertion      : 0.00
% 3.17/1.58  Index Deletion       : 0.00
% 3.17/1.58  Index Matching       : 0.00
% 3.17/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
