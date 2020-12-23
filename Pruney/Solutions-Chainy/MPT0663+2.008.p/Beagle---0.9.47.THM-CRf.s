%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   49 (  63 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  85 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r2_hidden('#skF_2',k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41,plain,(
    r2_hidden('#skF_2',k3_xboole_0('#skF_3',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_118,plain,(
    ! [C_60,B_61,A_62] :
      ( r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_2',B_70)
      | ~ r1_tarski(k3_xboole_0('#skF_3',k1_relat_1('#skF_4')),B_70) ) ),
    inference(resolution,[status(thm)],[c_41,c_118])).

tff(c_159,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_143])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_158,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_143])).

tff(c_26,plain,(
    ! [A_39,C_41,B_40] :
      ( r2_hidden(A_39,k1_relat_1(k7_relat_1(C_41,B_40)))
      | ~ r2_hidden(A_39,k1_relat_1(C_41))
      | ~ r2_hidden(A_39,B_40)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_548,plain,(
    ! [C_157,B_158,A_159] :
      ( k1_funct_1(k7_relat_1(C_157,B_158),A_159) = k1_funct_1(C_157,A_159)
      | ~ r2_hidden(A_159,k1_relat_1(k7_relat_1(C_157,B_158)))
      | ~ v1_funct_1(C_157)
      | ~ v1_relat_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_997,plain,(
    ! [C_213,B_214,A_215] :
      ( k1_funct_1(k7_relat_1(C_213,B_214),A_215) = k1_funct_1(C_213,A_215)
      | ~ v1_funct_1(C_213)
      | ~ r2_hidden(A_215,k1_relat_1(C_213))
      | ~ r2_hidden(A_215,B_214)
      | ~ v1_relat_1(C_213) ) ),
    inference(resolution,[status(thm)],[c_26,c_548])).

tff(c_1039,plain,(
    ! [B_214] :
      ( k1_funct_1(k7_relat_1('#skF_4',B_214),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden('#skF_2',B_214)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_158,c_997])).

tff(c_1076,plain,(
    ! [B_219] :
      ( k1_funct_1(k7_relat_1('#skF_4',B_219),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
      | ~ r2_hidden('#skF_2',B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1039])).

tff(c_34,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1082,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_34])).

tff(c_1090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/2.15  
% 4.50/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/2.16  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.50/2.16  
% 4.50/2.16  %Foreground sorts:
% 4.50/2.16  
% 4.50/2.16  
% 4.50/2.16  %Background operators:
% 4.50/2.16  
% 4.50/2.16  
% 4.50/2.16  %Foreground operators:
% 4.50/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.50/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/2.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.50/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.50/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/2.16  tff('#skF_2', type, '#skF_2': $i).
% 4.50/2.16  tff('#skF_3', type, '#skF_3': $i).
% 4.50/2.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.50/2.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.50/2.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.50/2.16  tff('#skF_4', type, '#skF_4': $i).
% 4.50/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/2.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.50/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.50/2.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.50/2.16  
% 4.50/2.17  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.50/2.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.50/2.17  tff(f_75, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 4.50/2.17  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.50/2.17  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 4.50/2.17  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 4.50/2.17  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.50/2.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/2.17  tff(c_36, plain, (r2_hidden('#skF_2', k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/2.17  tff(c_41, plain, (r2_hidden('#skF_2', k3_xboole_0('#skF_3', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 4.50/2.17  tff(c_118, plain, (![C_60, B_61, A_62]: (r2_hidden(C_60, B_61) | ~r2_hidden(C_60, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.50/2.17  tff(c_143, plain, (![B_70]: (r2_hidden('#skF_2', B_70) | ~r1_tarski(k3_xboole_0('#skF_3', k1_relat_1('#skF_4')), B_70))), inference(resolution, [status(thm)], [c_41, c_118])).
% 4.50/2.17  tff(c_159, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_143])).
% 4.50/2.17  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/2.17  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/2.17  tff(c_43, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/2.17  tff(c_58, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_43, c_10])).
% 4.50/2.17  tff(c_158, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_143])).
% 4.50/2.17  tff(c_26, plain, (![A_39, C_41, B_40]: (r2_hidden(A_39, k1_relat_1(k7_relat_1(C_41, B_40))) | ~r2_hidden(A_39, k1_relat_1(C_41)) | ~r2_hidden(A_39, B_40) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.50/2.17  tff(c_548, plain, (![C_157, B_158, A_159]: (k1_funct_1(k7_relat_1(C_157, B_158), A_159)=k1_funct_1(C_157, A_159) | ~r2_hidden(A_159, k1_relat_1(k7_relat_1(C_157, B_158))) | ~v1_funct_1(C_157) | ~v1_relat_1(C_157))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.50/2.17  tff(c_997, plain, (![C_213, B_214, A_215]: (k1_funct_1(k7_relat_1(C_213, B_214), A_215)=k1_funct_1(C_213, A_215) | ~v1_funct_1(C_213) | ~r2_hidden(A_215, k1_relat_1(C_213)) | ~r2_hidden(A_215, B_214) | ~v1_relat_1(C_213))), inference(resolution, [status(thm)], [c_26, c_548])).
% 4.50/2.17  tff(c_1039, plain, (![B_214]: (k1_funct_1(k7_relat_1('#skF_4', B_214), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~r2_hidden('#skF_2', B_214) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_158, c_997])).
% 4.50/2.17  tff(c_1076, plain, (![B_219]: (k1_funct_1(k7_relat_1('#skF_4', B_219), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_2', B_219))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1039])).
% 4.50/2.17  tff(c_34, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/2.17  tff(c_1082, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1076, c_34])).
% 4.50/2.17  tff(c_1090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_1082])).
% 4.50/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/2.17  
% 4.50/2.17  Inference rules
% 4.50/2.17  ----------------------
% 4.50/2.17  #Ref     : 0
% 4.50/2.17  #Sup     : 252
% 4.50/2.17  #Fact    : 0
% 4.50/2.17  #Define  : 0
% 4.50/2.17  #Split   : 0
% 4.50/2.17  #Chain   : 0
% 4.50/2.17  #Close   : 0
% 4.50/2.17  
% 4.50/2.17  Ordering : KBO
% 4.50/2.17  
% 4.50/2.17  Simplification rules
% 4.50/2.17  ----------------------
% 4.50/2.17  #Subsume      : 53
% 4.50/2.17  #Demod        : 28
% 4.50/2.17  #Tautology    : 50
% 4.50/2.17  #SimpNegUnit  : 0
% 4.50/2.17  #BackRed      : 0
% 4.50/2.17  
% 4.50/2.17  #Partial instantiations: 0
% 4.50/2.17  #Strategies tried      : 1
% 4.50/2.17  
% 4.50/2.17  Timing (in seconds)
% 4.50/2.17  ----------------------
% 4.70/2.18  Preprocessing        : 0.51
% 4.70/2.18  Parsing              : 0.27
% 4.70/2.18  CNF conversion       : 0.03
% 4.70/2.18  Main loop            : 0.79
% 4.70/2.18  Inferencing          : 0.27
% 4.70/2.18  Reduction            : 0.24
% 4.70/2.18  Demodulation         : 0.19
% 4.70/2.18  BG Simplification    : 0.04
% 4.70/2.18  Subsumption          : 0.19
% 4.70/2.18  Abstraction          : 0.05
% 4.70/2.18  MUC search           : 0.00
% 4.70/2.18  Cooper               : 0.00
% 4.70/2.18  Total                : 1.35
% 4.70/2.18  Index Insertion      : 0.00
% 4.70/2.18  Index Deletion       : 0.00
% 4.70/2.18  Index Matching       : 0.00
% 4.70/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
