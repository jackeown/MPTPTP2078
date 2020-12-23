%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  83 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,(
    ! [A_52] :
      ( k10_relat_1(A_52,k2_relat_1(A_52)) = k1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,(
    ! [A_30] :
      ( k10_relat_1(k6_relat_1(A_30),A_30) = k1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_110])).

tff(c_123,plain,(
    ! [A_30] : k10_relat_1(k6_relat_1(A_30),A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22,c_119])).

tff(c_185,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ r1_tarski(k1_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_198,plain,(
    ! [A_30,A_66] :
      ( k7_relat_1(k6_relat_1(A_30),A_66) = k6_relat_1(A_30)
      | ~ r1_tarski(A_30,A_66)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_203,plain,(
    ! [A_30,A_66] :
      ( k7_relat_1(k6_relat_1(A_30),A_66) = k6_relat_1(A_30)
      | ~ r1_tarski(A_30,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_198])).

tff(c_289,plain,(
    ! [A_76,C_77,B_78] :
      ( k3_xboole_0(A_76,k10_relat_1(C_77,B_78)) = k10_relat_1(k7_relat_1(C_77,A_76),B_78)
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_298,plain,(
    ! [A_30,A_76] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_30),A_76),A_30) = k3_xboole_0(A_76,A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_289])).

tff(c_306,plain,(
    ! [A_79,A_80] : k10_relat_1(k7_relat_1(k6_relat_1(A_79),A_80),A_79) = k3_xboole_0(A_80,A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_298])).

tff(c_318,plain,(
    ! [A_66,A_30] :
      ( k3_xboole_0(A_66,A_30) = k10_relat_1(k6_relat_1(A_30),A_30)
      | ~ r1_tarski(A_30,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_306])).

tff(c_373,plain,(
    ! [A_84,A_85] :
      ( k3_xboole_0(A_84,A_85) = A_85
      | ~ r1_tarski(A_85,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_318])).

tff(c_390,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_373])).

tff(c_32,plain,(
    ! [A_36,C_38,B_37] :
      ( k3_xboole_0(A_36,k10_relat_1(C_38,B_37)) = k10_relat_1(k7_relat_1(C_38,A_36),B_37)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_394,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_32])).

tff(c_401,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_394])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.45  
% 2.56/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.46  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.46  
% 2.56/1.46  %Foreground sorts:
% 2.56/1.46  
% 2.56/1.46  
% 2.56/1.46  %Background operators:
% 2.56/1.46  
% 2.56/1.46  
% 2.56/1.46  %Foreground operators:
% 2.56/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.56/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.56/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.56/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.56/1.46  
% 2.56/1.47  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.56/1.47  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.56/1.47  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.56/1.47  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.56/1.47  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.56/1.47  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.56/1.47  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.56/1.47  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.56/1.47  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.56/1.47  tff(c_16, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.47  tff(c_22, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.47  tff(c_24, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.47  tff(c_110, plain, (![A_52]: (k10_relat_1(A_52, k2_relat_1(A_52))=k1_relat_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.47  tff(c_119, plain, (![A_30]: (k10_relat_1(k6_relat_1(A_30), A_30)=k1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_110])).
% 2.56/1.47  tff(c_123, plain, (![A_30]: (k10_relat_1(k6_relat_1(A_30), A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22, c_119])).
% 2.56/1.47  tff(c_185, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~r1_tarski(k1_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.56/1.47  tff(c_198, plain, (![A_30, A_66]: (k7_relat_1(k6_relat_1(A_30), A_66)=k6_relat_1(A_30) | ~r1_tarski(A_30, A_66) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_185])).
% 2.56/1.47  tff(c_203, plain, (![A_30, A_66]: (k7_relat_1(k6_relat_1(A_30), A_66)=k6_relat_1(A_30) | ~r1_tarski(A_30, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_198])).
% 2.56/1.47  tff(c_289, plain, (![A_76, C_77, B_78]: (k3_xboole_0(A_76, k10_relat_1(C_77, B_78))=k10_relat_1(k7_relat_1(C_77, A_76), B_78) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.56/1.47  tff(c_298, plain, (![A_30, A_76]: (k10_relat_1(k7_relat_1(k6_relat_1(A_30), A_76), A_30)=k3_xboole_0(A_76, A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_289])).
% 2.56/1.47  tff(c_306, plain, (![A_79, A_80]: (k10_relat_1(k7_relat_1(k6_relat_1(A_79), A_80), A_79)=k3_xboole_0(A_80, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_298])).
% 2.56/1.47  tff(c_318, plain, (![A_66, A_30]: (k3_xboole_0(A_66, A_30)=k10_relat_1(k6_relat_1(A_30), A_30) | ~r1_tarski(A_30, A_66))), inference(superposition, [status(thm), theory('equality')], [c_203, c_306])).
% 2.56/1.47  tff(c_373, plain, (![A_84, A_85]: (k3_xboole_0(A_84, A_85)=A_85 | ~r1_tarski(A_85, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_318])).
% 2.56/1.47  tff(c_390, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_373])).
% 2.56/1.47  tff(c_32, plain, (![A_36, C_38, B_37]: (k3_xboole_0(A_36, k10_relat_1(C_38, B_37))=k10_relat_1(k7_relat_1(C_38, A_36), B_37) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.56/1.47  tff(c_394, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_390, c_32])).
% 2.56/1.47  tff(c_401, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_394])).
% 2.56/1.47  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_401])).
% 2.56/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.47  
% 2.56/1.47  Inference rules
% 2.56/1.47  ----------------------
% 2.56/1.47  #Ref     : 0
% 2.56/1.47  #Sup     : 77
% 2.56/1.47  #Fact    : 0
% 2.56/1.47  #Define  : 0
% 2.56/1.47  #Split   : 0
% 2.56/1.47  #Chain   : 0
% 2.56/1.47  #Close   : 0
% 2.56/1.47  
% 2.56/1.47  Ordering : KBO
% 2.56/1.47  
% 2.56/1.47  Simplification rules
% 2.56/1.47  ----------------------
% 2.56/1.47  #Subsume      : 6
% 2.56/1.47  #Demod        : 44
% 2.56/1.47  #Tautology    : 45
% 2.56/1.47  #SimpNegUnit  : 1
% 2.56/1.47  #BackRed      : 0
% 2.56/1.47  
% 2.56/1.47  #Partial instantiations: 0
% 2.56/1.47  #Strategies tried      : 1
% 2.56/1.47  
% 2.56/1.47  Timing (in seconds)
% 2.56/1.47  ----------------------
% 2.56/1.47  Preprocessing        : 0.38
% 2.56/1.47  Parsing              : 0.18
% 2.56/1.47  CNF conversion       : 0.03
% 2.56/1.47  Main loop            : 0.30
% 2.56/1.47  Inferencing          : 0.10
% 2.56/1.47  Reduction            : 0.10
% 2.56/1.47  Demodulation         : 0.07
% 2.56/1.47  BG Simplification    : 0.02
% 2.56/1.47  Subsumption          : 0.05
% 2.56/1.47  Abstraction          : 0.03
% 2.56/1.47  MUC search           : 0.00
% 2.56/1.47  Cooper               : 0.00
% 2.56/1.47  Total                : 0.72
% 2.56/1.47  Index Insertion      : 0.00
% 2.56/1.47  Index Deletion       : 0.00
% 2.56/1.47  Index Matching       : 0.00
% 2.56/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
