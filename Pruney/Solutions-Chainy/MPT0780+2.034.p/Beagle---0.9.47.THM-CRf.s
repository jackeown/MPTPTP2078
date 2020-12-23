%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:43 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  70 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_89,plain,(
    ! [A_39,B_40] :
      ( k5_relat_1(k6_relat_1(A_39),B_40) = k7_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_relat_1(B_19),k6_relat_1(A_18)) = k6_relat_1(k3_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [A_18,A_39] :
      ( k7_relat_1(k6_relat_1(A_18),A_39) = k6_relat_1(k3_xboole_0(A_18,A_39))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_22])).

tff(c_105,plain,(
    ! [A_18,A_39] : k7_relat_1(k6_relat_1(A_18),A_39) = k6_relat_1(k3_xboole_0(A_18,A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_96])).

tff(c_119,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ r1_tarski(k1_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [A_12,A_44] :
      ( k7_relat_1(k6_relat_1(A_12),A_44) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_44)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_119])).

tff(c_134,plain,(
    ! [A_49,A_50] :
      ( k6_relat_1(k3_xboole_0(A_49,A_50)) = k6_relat_1(A_49)
      | ~ r1_tarski(A_49,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_105,c_122])).

tff(c_152,plain,(
    ! [A_49,A_50] :
      ( k3_xboole_0(A_49,A_50) = k1_relat_1(k6_relat_1(A_49))
      | ~ r1_tarski(A_49,A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_10])).

tff(c_172,plain,(
    ! [A_51,A_52] :
      ( k3_xboole_0(A_51,A_52) = A_51
      | ~ r1_tarski(A_51,A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_176,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_24,plain,(
    ! [C_22,A_20,B_21] :
      ( k2_wellord1(k2_wellord1(C_22,A_20),B_21) = k2_wellord1(C_22,k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_207,plain,(
    ! [C_56,B_57,A_58] :
      ( k2_wellord1(k2_wellord1(C_56,B_57),A_58) = k2_wellord1(k2_wellord1(C_56,A_58),B_57)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_246,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_28])).

tff(c_291,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_246])).

tff(c_300,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_291])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_176,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.26  
% 2.08/1.26  %Foreground sorts:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Background operators:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Foreground operators:
% 2.08/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.08/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.08/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.26  
% 2.08/1.27  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 2.08/1.27  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.08/1.27  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.08/1.27  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.08/1.27  tff(f_53, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.08/1.27  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.08/1.27  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 2.08/1.27  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 2.08/1.27  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.27  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.27  tff(c_10, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.27  tff(c_18, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.27  tff(c_89, plain, (![A_39, B_40]: (k5_relat_1(k6_relat_1(A_39), B_40)=k7_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.27  tff(c_22, plain, (![B_19, A_18]: (k5_relat_1(k6_relat_1(B_19), k6_relat_1(A_18))=k6_relat_1(k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.27  tff(c_96, plain, (![A_18, A_39]: (k7_relat_1(k6_relat_1(A_18), A_39)=k6_relat_1(k3_xboole_0(A_18, A_39)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_22])).
% 2.08/1.27  tff(c_105, plain, (![A_18, A_39]: (k7_relat_1(k6_relat_1(A_18), A_39)=k6_relat_1(k3_xboole_0(A_18, A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_96])).
% 2.08/1.27  tff(c_119, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~r1_tarski(k1_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.27  tff(c_122, plain, (![A_12, A_44]: (k7_relat_1(k6_relat_1(A_12), A_44)=k6_relat_1(A_12) | ~r1_tarski(A_12, A_44) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_119])).
% 2.08/1.27  tff(c_134, plain, (![A_49, A_50]: (k6_relat_1(k3_xboole_0(A_49, A_50))=k6_relat_1(A_49) | ~r1_tarski(A_49, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_105, c_122])).
% 2.08/1.27  tff(c_152, plain, (![A_49, A_50]: (k3_xboole_0(A_49, A_50)=k1_relat_1(k6_relat_1(A_49)) | ~r1_tarski(A_49, A_50))), inference(superposition, [status(thm), theory('equality')], [c_134, c_10])).
% 2.08/1.27  tff(c_172, plain, (![A_51, A_52]: (k3_xboole_0(A_51, A_52)=A_51 | ~r1_tarski(A_51, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_152])).
% 2.08/1.27  tff(c_176, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_30, c_172])).
% 2.08/1.27  tff(c_24, plain, (![C_22, A_20, B_21]: (k2_wellord1(k2_wellord1(C_22, A_20), B_21)=k2_wellord1(C_22, k3_xboole_0(A_20, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.27  tff(c_207, plain, (![C_56, B_57, A_58]: (k2_wellord1(k2_wellord1(C_56, B_57), A_58)=k2_wellord1(k2_wellord1(C_56, A_58), B_57) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.27  tff(c_28, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.27  tff(c_246, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_28])).
% 2.08/1.27  tff(c_291, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_246])).
% 2.08/1.27  tff(c_300, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_291])).
% 2.08/1.27  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_176, c_300])).
% 2.08/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  Inference rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Ref     : 0
% 2.08/1.27  #Sup     : 67
% 2.08/1.27  #Fact    : 0
% 2.08/1.27  #Define  : 0
% 2.08/1.27  #Split   : 0
% 2.08/1.27  #Chain   : 0
% 2.08/1.27  #Close   : 0
% 2.08/1.27  
% 2.08/1.27  Ordering : KBO
% 2.08/1.27  
% 2.08/1.27  Simplification rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Subsume      : 1
% 2.08/1.27  #Demod        : 18
% 2.08/1.27  #Tautology    : 36
% 2.08/1.27  #SimpNegUnit  : 0
% 2.08/1.27  #BackRed      : 0
% 2.08/1.27  
% 2.08/1.27  #Partial instantiations: 0
% 2.08/1.27  #Strategies tried      : 1
% 2.08/1.27  
% 2.08/1.27  Timing (in seconds)
% 2.08/1.27  ----------------------
% 2.08/1.28  Preprocessing        : 0.31
% 2.08/1.28  Parsing              : 0.17
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.20
% 2.08/1.28  Inferencing          : 0.09
% 2.08/1.28  Reduction            : 0.06
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.02
% 2.08/1.28  Subsumption          : 0.03
% 2.08/1.28  Abstraction          : 0.02
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.54
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
