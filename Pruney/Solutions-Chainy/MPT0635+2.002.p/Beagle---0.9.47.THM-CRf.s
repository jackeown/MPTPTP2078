%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 139 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_42,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_106,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_106])).

tff(c_16,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_136,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_153,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_38])).

tff(c_221,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_251,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_3',B_60)
      | ~ r1_tarski(k3_xboole_0('#skF_4',k1_relat_1('#skF_5')),B_60) ) ),
    inference(resolution,[status(thm)],[c_153,c_221])).

tff(c_267,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_251])).

tff(c_22,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_18] : v1_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [A_23,C_27] :
      ( k1_funct_1(k6_relat_1(A_23),C_27) = C_27
      | ~ r2_hidden(C_27,A_23)
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    ! [A_23,C_27] :
      ( k1_funct_1(k6_relat_1(A_23),C_27) = C_27
      | ~ r2_hidden(C_27,A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_48,plain,(
    ! [A_23,C_27] :
      ( k1_funct_1(k6_relat_1(A_23),C_27) = C_27
      | ~ r2_hidden(C_27,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [A_23] :
      ( k1_relat_1(k6_relat_1(A_23)) = A_23
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [A_23] :
      ( k1_relat_1(k6_relat_1(A_23)) = A_23
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_50,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_44])).

tff(c_341,plain,(
    ! [B_77,C_78,A_79] :
      ( k1_funct_1(k5_relat_1(B_77,C_78),A_79) = k1_funct_1(C_78,k1_funct_1(B_77,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(B_77))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_356,plain,(
    ! [A_23,C_78,A_79] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_23),C_78),A_79) = k1_funct_1(C_78,k1_funct_1(k6_relat_1(A_23),A_79))
      | ~ r2_hidden(A_79,A_23)
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_341])).

tff(c_573,plain,(
    ! [A_113,C_114,A_115] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_113),C_114),A_115) = k1_funct_1(C_114,k1_funct_1(k6_relat_1(A_113),A_115))
      | ~ r2_hidden(A_115,A_113)
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_356])).

tff(c_36,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_583,plain,
    ( k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_36])).

tff(c_589,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_267,c_583])).

tff(c_593,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_589])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:02:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.84  
% 3.31/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.85  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.31/1.85  
% 3.31/1.85  %Foreground sorts:
% 3.31/1.85  
% 3.31/1.85  
% 3.31/1.85  %Background operators:
% 3.31/1.85  
% 3.31/1.85  
% 3.31/1.85  %Foreground operators:
% 3.31/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.85  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.85  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.31/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.85  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.31/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.31/1.85  
% 3.31/1.86  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.31/1.86  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.31/1.86  tff(f_42, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.31/1.86  tff(f_85, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 3.31/1.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.86  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.31/1.86  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 3.31/1.86  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.31/1.86  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.31/1.86  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.31/1.86  tff(c_106, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.86  tff(c_130, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_10, c_106])).
% 3.31/1.86  tff(c_16, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.86  tff(c_136, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 3.31/1.86  tff(c_38, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.31/1.86  tff(c_153, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_38])).
% 3.31/1.86  tff(c_221, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.86  tff(c_251, plain, (![B_60]: (r2_hidden('#skF_3', B_60) | ~r1_tarski(k3_xboole_0('#skF_4', k1_relat_1('#skF_5')), B_60))), inference(resolution, [status(thm)], [c_153, c_221])).
% 3.31/1.86  tff(c_267, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_251])).
% 3.31/1.86  tff(c_22, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.86  tff(c_24, plain, (![A_18]: (v1_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.86  tff(c_32, plain, (![A_23, C_27]: (k1_funct_1(k6_relat_1(A_23), C_27)=C_27 | ~r2_hidden(C_27, A_23) | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.31/1.86  tff(c_46, plain, (![A_23, C_27]: (k1_funct_1(k6_relat_1(A_23), C_27)=C_27 | ~r2_hidden(C_27, A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 3.31/1.86  tff(c_48, plain, (![A_23, C_27]: (k1_funct_1(k6_relat_1(A_23), C_27)=C_27 | ~r2_hidden(C_27, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_46])).
% 3.31/1.86  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.31/1.86  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.31/1.86  tff(c_34, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23 | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.31/1.86  tff(c_44, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23 | ~v1_relat_1(k6_relat_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 3.31/1.86  tff(c_50, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_44])).
% 3.31/1.86  tff(c_341, plain, (![B_77, C_78, A_79]: (k1_funct_1(k5_relat_1(B_77, C_78), A_79)=k1_funct_1(C_78, k1_funct_1(B_77, A_79)) | ~r2_hidden(A_79, k1_relat_1(B_77)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.31/1.86  tff(c_356, plain, (![A_23, C_78, A_79]: (k1_funct_1(k5_relat_1(k6_relat_1(A_23), C_78), A_79)=k1_funct_1(C_78, k1_funct_1(k6_relat_1(A_23), A_79)) | ~r2_hidden(A_79, A_23) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_341])).
% 3.31/1.86  tff(c_573, plain, (![A_113, C_114, A_115]: (k1_funct_1(k5_relat_1(k6_relat_1(A_113), C_114), A_115)=k1_funct_1(C_114, k1_funct_1(k6_relat_1(A_113), A_115)) | ~r2_hidden(A_115, A_113) | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_356])).
% 3.31/1.86  tff(c_36, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.31/1.86  tff(c_583, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_573, c_36])).
% 3.31/1.86  tff(c_589, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_267, c_583])).
% 3.31/1.86  tff(c_593, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_589])).
% 3.31/1.86  tff(c_597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_593])).
% 3.31/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.86  
% 3.31/1.86  Inference rules
% 3.31/1.86  ----------------------
% 3.31/1.86  #Ref     : 0
% 3.31/1.86  #Sup     : 132
% 3.31/1.87  #Fact    : 0
% 3.31/1.87  #Define  : 0
% 3.31/1.87  #Split   : 0
% 3.31/1.87  #Chain   : 0
% 3.31/1.87  #Close   : 0
% 3.31/1.87  
% 3.31/1.87  Ordering : KBO
% 3.31/1.87  
% 3.31/1.87  Simplification rules
% 3.31/1.87  ----------------------
% 3.31/1.87  #Subsume      : 22
% 3.31/1.87  #Demod        : 48
% 3.31/1.87  #Tautology    : 53
% 3.31/1.87  #SimpNegUnit  : 0
% 3.31/1.87  #BackRed      : 1
% 3.31/1.87  
% 3.31/1.87  #Partial instantiations: 0
% 3.31/1.87  #Strategies tried      : 1
% 3.31/1.87  
% 3.31/1.87  Timing (in seconds)
% 3.31/1.87  ----------------------
% 3.31/1.87  Preprocessing        : 0.48
% 3.31/1.87  Parsing              : 0.24
% 3.31/1.87  CNF conversion       : 0.03
% 3.31/1.87  Main loop            : 0.50
% 3.31/1.87  Inferencing          : 0.17
% 3.31/1.87  Reduction            : 0.17
% 3.31/1.87  Demodulation         : 0.13
% 3.31/1.87  BG Simplification    : 0.03
% 3.31/1.87  Subsumption          : 0.10
% 3.31/1.87  Abstraction          : 0.03
% 3.31/1.87  MUC search           : 0.00
% 3.31/1.87  Cooper               : 0.00
% 3.31/1.87  Total                : 1.03
% 3.31/1.87  Index Insertion      : 0.00
% 3.31/1.87  Index Deletion       : 0.00
% 3.31/1.87  Index Matching       : 0.00
% 3.31/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
