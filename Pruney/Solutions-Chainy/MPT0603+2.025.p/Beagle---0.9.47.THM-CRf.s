%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:27 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  65 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_28,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_99,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(k7_relat_1(A_56,B_57))
      | ~ v1_xboole_0(B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_57,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_184,plain,(
    ! [A_67,B_68] :
      ( k7_relat_1(A_67,B_68) = k1_xboole_0
      | ~ v1_xboole_0(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_99,c_60])).

tff(c_191,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_2,c_184])).

tff(c_199,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_191])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_108,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_129,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_38,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_86])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_108])).

tff(c_170,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_123])).

tff(c_273,plain,(
    ! [C_79,A_80,B_81] :
      ( k7_relat_1(k7_relat_1(C_79,A_80),B_81) = k7_relat_1(C_79,k3_xboole_0(A_80,B_81))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_288,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_36])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_199,c_170,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.34  
% 2.23/1.35  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.23/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.35  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.23/1.35  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.23/1.35  tff(f_28, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.23/1.35  tff(f_30, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.23/1.35  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/1.35  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.23/1.35  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.23/1.35  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.35  tff(c_99, plain, (![A_56, B_57]: (v1_xboole_0(k7_relat_1(A_56, B_57)) | ~v1_xboole_0(B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.35  tff(c_57, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.35  tff(c_60, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.23/1.35  tff(c_184, plain, (![A_67, B_68]: (k7_relat_1(A_67, B_68)=k1_xboole_0 | ~v1_xboole_0(B_68) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_99, c_60])).
% 2.23/1.35  tff(c_191, plain, (![A_69]: (k7_relat_1(A_69, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_2, c_184])).
% 2.23/1.35  tff(c_199, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_191])).
% 2.23/1.35  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.23/1.35  tff(c_6, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.23/1.35  tff(c_108, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.35  tff(c_126, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_108])).
% 2.23/1.35  tff(c_129, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 2.23/1.35  tff(c_38, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.35  tff(c_86, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.35  tff(c_94, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_86])).
% 2.23/1.35  tff(c_123, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_94, c_108])).
% 2.23/1.35  tff(c_170, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_123])).
% 2.23/1.35  tff(c_273, plain, (![C_79, A_80, B_81]: (k7_relat_1(k7_relat_1(C_79, A_80), B_81)=k7_relat_1(C_79, k3_xboole_0(A_80, B_81)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.35  tff(c_36, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.35  tff(c_288, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_273, c_36])).
% 2.23/1.35  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_199, c_170, c_288])).
% 2.23/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  Inference rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Ref     : 0
% 2.23/1.35  #Sup     : 67
% 2.23/1.35  #Fact    : 0
% 2.23/1.35  #Define  : 0
% 2.23/1.35  #Split   : 0
% 2.23/1.36  #Chain   : 0
% 2.23/1.36  #Close   : 0
% 2.23/1.36  
% 2.23/1.36  Ordering : KBO
% 2.23/1.36  
% 2.23/1.36  Simplification rules
% 2.23/1.36  ----------------------
% 2.23/1.36  #Subsume      : 1
% 2.23/1.36  #Demod        : 27
% 2.23/1.36  #Tautology    : 42
% 2.23/1.36  #SimpNegUnit  : 0
% 2.23/1.36  #BackRed      : 0
% 2.23/1.36  
% 2.23/1.36  #Partial instantiations: 0
% 2.23/1.36  #Strategies tried      : 1
% 2.23/1.36  
% 2.23/1.36  Timing (in seconds)
% 2.23/1.36  ----------------------
% 2.23/1.36  Preprocessing        : 0.36
% 2.23/1.36  Parsing              : 0.18
% 2.23/1.36  CNF conversion       : 0.02
% 2.23/1.36  Main loop            : 0.18
% 2.23/1.36  Inferencing          : 0.07
% 2.23/1.36  Reduction            : 0.05
% 2.23/1.36  Demodulation         : 0.04
% 2.23/1.36  BG Simplification    : 0.02
% 2.23/1.36  Subsumption          : 0.03
% 2.23/1.36  Abstraction          : 0.01
% 2.23/1.36  MUC search           : 0.00
% 2.23/1.36  Cooper               : 0.00
% 2.23/1.36  Total                : 0.56
% 2.23/1.36  Index Insertion      : 0.00
% 2.23/1.36  Index Deletion       : 0.00
% 2.23/1.36  Index Matching       : 0.00
% 2.23/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
