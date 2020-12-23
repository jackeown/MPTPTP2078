%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 100 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 144 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(B_33,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [B_33,A_32] : k3_xboole_0(B_33,A_32) = k3_xboole_0(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_32,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_137,plain,(
    r2_hidden('#skF_1',k3_xboole_0('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_32])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_190,plain,(
    ! [A_41,B_42] :
      ( k5_relat_1(k6_relat_1(A_41),B_42) = k7_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [B_18,A_17] : k5_relat_1(k6_relat_1(B_18),k6_relat_1(A_17)) = k6_relat_1(k3_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    ! [A_17,A_41] :
      ( k7_relat_1(k6_relat_1(A_17),A_41) = k6_relat_1(k3_xboole_0(A_17,A_41))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_26])).

tff(c_211,plain,(
    ! [A_46,A_47] : k7_relat_1(k6_relat_1(A_46),A_47) = k6_relat_1(k3_xboole_0(A_46,A_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_197])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(A_11,B_12)
      | ~ r2_hidden(A_11,k1_relat_1(k7_relat_1(C_13,B_12)))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_217,plain,(
    ! [A_11,A_47,A_46] :
      ( r2_hidden(A_11,A_47)
      | ~ r2_hidden(A_11,k1_relat_1(k6_relat_1(k3_xboole_0(A_46,A_47))))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_18])).

tff(c_226,plain,(
    ! [A_48,A_49,A_50] :
      ( r2_hidden(A_48,A_49)
      | ~ r2_hidden(A_48,k3_xboole_0(A_50,A_49)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10,c_217])).

tff(c_237,plain,(
    ! [A_51,B_52,A_53] :
      ( r2_hidden(A_51,B_52)
      | ~ r2_hidden(A_51,k3_xboole_0(B_52,A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_226])).

tff(c_247,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_137,c_237])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_236,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_137,c_226])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r2_hidden(A_11,k1_relat_1(k7_relat_1(C_13,B_12)))
      | ~ r2_hidden(A_11,k1_relat_1(C_13))
      | ~ r2_hidden(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_268,plain,(
    ! [C_60,B_61,A_62] :
      ( k1_funct_1(k7_relat_1(C_60,B_61),A_62) = k1_funct_1(C_60,A_62)
      | ~ r2_hidden(A_62,k1_relat_1(k7_relat_1(C_60,B_61)))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_342,plain,(
    ! [C_75,B_76,A_77] :
      ( k1_funct_1(k7_relat_1(C_75,B_76),A_77) = k1_funct_1(C_75,A_77)
      | ~ v1_funct_1(C_75)
      | ~ r2_hidden(A_77,k1_relat_1(C_75))
      | ~ r2_hidden(A_77,B_76)
      | ~ v1_relat_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_14,c_268])).

tff(c_346,plain,(
    ! [B_76] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_76),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden('#skF_1',B_76)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_236,c_342])).

tff(c_359,plain,(
    ! [B_78] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_78),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ r2_hidden('#skF_1',B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_346])).

tff(c_30,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_365,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_30])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:16:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  
% 2.27/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.33  
% 2.27/1.33  %Foreground sorts:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Background operators:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Foreground operators:
% 2.27/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.27/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.27/1.34  
% 2.27/1.35  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.27/1.35  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.27/1.35  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 2.27/1.35  tff(f_53, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.27/1.35  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.27/1.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.27/1.35  tff(f_55, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.27/1.35  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.27/1.35  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.27/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.35  tff(c_90, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.35  tff(c_114, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(B_33, A_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 2.27/1.35  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.35  tff(c_120, plain, (![B_33, A_32]: (k3_xboole_0(B_33, A_32)=k3_xboole_0(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 2.27/1.35  tff(c_32, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.35  tff(c_137, plain, (r2_hidden('#skF_1', k3_xboole_0('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_32])).
% 2.27/1.35  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.35  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.35  tff(c_190, plain, (![A_41, B_42]: (k5_relat_1(k6_relat_1(A_41), B_42)=k7_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.35  tff(c_26, plain, (![B_18, A_17]: (k5_relat_1(k6_relat_1(B_18), k6_relat_1(A_17))=k6_relat_1(k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.35  tff(c_197, plain, (![A_17, A_41]: (k7_relat_1(k6_relat_1(A_17), A_41)=k6_relat_1(k3_xboole_0(A_17, A_41)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_26])).
% 2.27/1.35  tff(c_211, plain, (![A_46, A_47]: (k7_relat_1(k6_relat_1(A_46), A_47)=k6_relat_1(k3_xboole_0(A_46, A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_197])).
% 2.27/1.35  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden(A_11, B_12) | ~r2_hidden(A_11, k1_relat_1(k7_relat_1(C_13, B_12))) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.35  tff(c_217, plain, (![A_11, A_47, A_46]: (r2_hidden(A_11, A_47) | ~r2_hidden(A_11, k1_relat_1(k6_relat_1(k3_xboole_0(A_46, A_47)))) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_18])).
% 2.27/1.35  tff(c_226, plain, (![A_48, A_49, A_50]: (r2_hidden(A_48, A_49) | ~r2_hidden(A_48, k3_xboole_0(A_50, A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10, c_217])).
% 2.27/1.35  tff(c_237, plain, (![A_51, B_52, A_53]: (r2_hidden(A_51, B_52) | ~r2_hidden(A_51, k3_xboole_0(B_52, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_226])).
% 2.27/1.35  tff(c_247, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_137, c_237])).
% 2.27/1.35  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.35  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.35  tff(c_236, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_137, c_226])).
% 2.27/1.35  tff(c_14, plain, (![A_11, C_13, B_12]: (r2_hidden(A_11, k1_relat_1(k7_relat_1(C_13, B_12))) | ~r2_hidden(A_11, k1_relat_1(C_13)) | ~r2_hidden(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.35  tff(c_268, plain, (![C_60, B_61, A_62]: (k1_funct_1(k7_relat_1(C_60, B_61), A_62)=k1_funct_1(C_60, A_62) | ~r2_hidden(A_62, k1_relat_1(k7_relat_1(C_60, B_61))) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.35  tff(c_342, plain, (![C_75, B_76, A_77]: (k1_funct_1(k7_relat_1(C_75, B_76), A_77)=k1_funct_1(C_75, A_77) | ~v1_funct_1(C_75) | ~r2_hidden(A_77, k1_relat_1(C_75)) | ~r2_hidden(A_77, B_76) | ~v1_relat_1(C_75))), inference(resolution, [status(thm)], [c_14, c_268])).
% 2.27/1.35  tff(c_346, plain, (![B_76]: (k1_funct_1(k7_relat_1('#skF_3', B_76), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~r2_hidden('#skF_1', B_76) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_236, c_342])).
% 2.27/1.35  tff(c_359, plain, (![B_78]: (k1_funct_1(k7_relat_1('#skF_3', B_78), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', B_78))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_346])).
% 2.27/1.35  tff(c_30, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.35  tff(c_365, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_359, c_30])).
% 2.27/1.35  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_365])).
% 2.27/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  Inference rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Ref     : 0
% 2.27/1.35  #Sup     : 81
% 2.27/1.35  #Fact    : 0
% 2.27/1.35  #Define  : 0
% 2.27/1.35  #Split   : 0
% 2.27/1.35  #Chain   : 0
% 2.27/1.35  #Close   : 0
% 2.27/1.35  
% 2.27/1.35  Ordering : KBO
% 2.27/1.35  
% 2.27/1.35  Simplification rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Subsume      : 10
% 2.27/1.35  #Demod        : 27
% 2.27/1.35  #Tautology    : 49
% 2.27/1.35  #SimpNegUnit  : 0
% 2.27/1.35  #BackRed      : 1
% 2.27/1.35  
% 2.27/1.35  #Partial instantiations: 0
% 2.27/1.35  #Strategies tried      : 1
% 2.27/1.35  
% 2.27/1.35  Timing (in seconds)
% 2.27/1.35  ----------------------
% 2.27/1.35  Preprocessing        : 0.33
% 2.27/1.35  Parsing              : 0.18
% 2.27/1.35  CNF conversion       : 0.02
% 2.27/1.35  Main loop            : 0.22
% 2.27/1.35  Inferencing          : 0.08
% 2.27/1.35  Reduction            : 0.08
% 2.27/1.35  Demodulation         : 0.06
% 2.27/1.35  BG Simplification    : 0.01
% 2.27/1.35  Subsumption          : 0.03
% 2.27/1.35  Abstraction          : 0.01
% 2.27/1.35  MUC search           : 0.00
% 2.27/1.35  Cooper               : 0.00
% 2.27/1.35  Total                : 0.57
% 2.27/1.35  Index Insertion      : 0.00
% 2.27/1.35  Index Deletion       : 0.00
% 2.27/1.35  Index Matching       : 0.00
% 2.27/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
