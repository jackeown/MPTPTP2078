%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  95 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [D_32,A_33,B_34] :
      ( r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k4_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [D_35,A_36,B_37] :
      ( r2_hidden(D_35,A_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_36,B_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_125])).

tff(c_139,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_129])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( k1_funct_1(k6_relat_1(B_18),A_17) = A_17
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_12] : v1_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_698,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_funct_1(k5_relat_1(B_79,C_80),A_81) = k1_funct_1(C_80,k1_funct_1(B_79,A_81))
      | ~ r2_hidden(A_81,k1_relat_1(B_79))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_720,plain,(
    ! [A_11,C_80,A_81] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_11),C_80),A_81) = k1_funct_1(C_80,k1_funct_1(k6_relat_1(A_11),A_81))
      | ~ r2_hidden(A_81,A_11)
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_698])).

tff(c_1946,plain,(
    ! [A_144,C_145,A_146] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_144),C_145),A_146) = k1_funct_1(C_145,k1_funct_1(k6_relat_1(A_144),A_146))
      | ~ r2_hidden(A_146,A_144)
      | ~ v1_funct_1(C_145)
      | ~ v1_relat_1(C_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_720])).

tff(c_36,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1952,plain,
    ( k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1946,c_36])).

tff(c_1958,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_139,c_1952])).

tff(c_1962,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1958])).

tff(c_1966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_1962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.64  
% 4.07/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.64  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.07/1.64  
% 4.07/1.64  %Foreground sorts:
% 4.07/1.64  
% 4.07/1.64  
% 4.07/1.64  %Background operators:
% 4.07/1.64  
% 4.07/1.64  
% 4.07/1.64  %Foreground operators:
% 4.07/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.07/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.07/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.07/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/1.64  tff('#skF_5', type, '#skF_5': $i).
% 4.07/1.64  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.07/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.07/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.64  tff('#skF_4', type, '#skF_4': $i).
% 4.07/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.07/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/1.64  
% 4.07/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.07/1.65  tff(f_73, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 4.07/1.65  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.07/1.65  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.07/1.65  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 4.07/1.65  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.07/1.65  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.07/1.65  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 4.07/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.65  tff(c_38, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.07/1.65  tff(c_43, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 4.07/1.65  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.65  tff(c_125, plain, (![D_32, A_33, B_34]: (r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k4_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.65  tff(c_129, plain, (![D_35, A_36, B_37]: (r2_hidden(D_35, A_36) | ~r2_hidden(D_35, k3_xboole_0(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_125])).
% 4.07/1.65  tff(c_139, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_43, c_129])).
% 4.07/1.65  tff(c_34, plain, (![B_18, A_17]: (k1_funct_1(k6_relat_1(B_18), A_17)=A_17 | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.65  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.07/1.65  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.07/1.65  tff(c_28, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.07/1.65  tff(c_30, plain, (![A_12]: (v1_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.07/1.65  tff(c_24, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.07/1.65  tff(c_698, plain, (![B_79, C_80, A_81]: (k1_funct_1(k5_relat_1(B_79, C_80), A_81)=k1_funct_1(C_80, k1_funct_1(B_79, A_81)) | ~r2_hidden(A_81, k1_relat_1(B_79)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.07/1.65  tff(c_720, plain, (![A_11, C_80, A_81]: (k1_funct_1(k5_relat_1(k6_relat_1(A_11), C_80), A_81)=k1_funct_1(C_80, k1_funct_1(k6_relat_1(A_11), A_81)) | ~r2_hidden(A_81, A_11) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_698])).
% 4.07/1.65  tff(c_1946, plain, (![A_144, C_145, A_146]: (k1_funct_1(k5_relat_1(k6_relat_1(A_144), C_145), A_146)=k1_funct_1(C_145, k1_funct_1(k6_relat_1(A_144), A_146)) | ~r2_hidden(A_146, A_144) | ~v1_funct_1(C_145) | ~v1_relat_1(C_145))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_720])).
% 4.07/1.65  tff(c_36, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.07/1.65  tff(c_1952, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1946, c_36])).
% 4.07/1.65  tff(c_1958, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_139, c_1952])).
% 4.07/1.65  tff(c_1962, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1958])).
% 4.07/1.65  tff(c_1966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_1962])).
% 4.07/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.65  
% 4.07/1.65  Inference rules
% 4.07/1.65  ----------------------
% 4.07/1.65  #Ref     : 0
% 4.07/1.65  #Sup     : 492
% 4.07/1.65  #Fact    : 0
% 4.07/1.65  #Define  : 0
% 4.07/1.65  #Split   : 0
% 4.07/1.65  #Chain   : 0
% 4.07/1.65  #Close   : 0
% 4.07/1.65  
% 4.07/1.65  Ordering : KBO
% 4.07/1.65  
% 4.07/1.65  Simplification rules
% 4.07/1.65  ----------------------
% 4.07/1.65  #Subsume      : 104
% 4.07/1.65  #Demod        : 68
% 4.07/1.65  #Tautology    : 65
% 4.07/1.65  #SimpNegUnit  : 1
% 4.07/1.65  #BackRed      : 0
% 4.07/1.65  
% 4.07/1.65  #Partial instantiations: 0
% 4.07/1.65  #Strategies tried      : 1
% 4.07/1.65  
% 4.07/1.65  Timing (in seconds)
% 4.07/1.65  ----------------------
% 4.07/1.65  Preprocessing        : 0.27
% 4.07/1.65  Parsing              : 0.15
% 4.07/1.66  CNF conversion       : 0.02
% 4.07/1.66  Main loop            : 0.62
% 4.07/1.66  Inferencing          : 0.20
% 4.07/1.66  Reduction            : 0.21
% 4.07/1.66  Demodulation         : 0.17
% 4.07/1.66  BG Simplification    : 0.03
% 4.07/1.66  Subsumption          : 0.13
% 4.07/1.66  Abstraction          : 0.03
% 4.07/1.66  MUC search           : 0.00
% 4.07/1.66  Cooper               : 0.00
% 4.07/1.66  Total                : 0.92
% 4.07/1.66  Index Insertion      : 0.00
% 4.07/1.66  Index Deletion       : 0.00
% 4.07/1.66  Index Matching       : 0.00
% 4.07/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
