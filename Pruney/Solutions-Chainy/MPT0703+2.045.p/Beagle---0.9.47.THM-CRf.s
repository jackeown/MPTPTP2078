%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 124 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))) = k3_xboole_0(k9_relat_1(C,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_167,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_175,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_20])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_318,plain,(
    ! [B_38,A_39] :
      ( k9_relat_1(B_38,k10_relat_1(B_38,A_39)) = A_39
      | ~ r1_tarski(A_39,k2_relat_1(B_38))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_332,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_318])).

tff(c_339,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_332])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_4])).

tff(c_255,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_283,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_255])).

tff(c_305,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_283])).

tff(c_18,plain,(
    ! [C_16,A_14,B_15] :
      ( k9_relat_1(C_16,k3_xboole_0(A_14,k10_relat_1(C_16,B_15))) = k3_xboole_0(k9_relat_1(C_16,A_14),B_15)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_664,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')),'#skF_2') = k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_18])).

tff(c_675,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_339,c_339,c_664])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_789,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_57,B_58),k3_xboole_0(A_57,B_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_8])).

tff(c_798,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_789])).

tff(c_850,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_798])).

tff(c_852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.35  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.31/1.35  
% 2.31/1.35  %Foreground sorts:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Background operators:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Foreground operators:
% 2.31/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.31/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.35  
% 2.31/1.36  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.31/1.36  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 2.31/1.36  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.31/1.36  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.31/1.36  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.31/1.36  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.31/1.36  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))) = k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_funct_1)).
% 2.31/1.36  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.31/1.36  tff(c_167, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.36  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.36  tff(c_175, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_20])).
% 2.31/1.36  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.36  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.36  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.36  tff(c_22, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.36  tff(c_318, plain, (![B_38, A_39]: (k9_relat_1(B_38, k10_relat_1(B_38, A_39))=A_39 | ~r1_tarski(A_39, k2_relat_1(B_38)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.36  tff(c_332, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_318])).
% 2.31/1.36  tff(c_339, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_332])).
% 2.31/1.36  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.36  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.36  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.36  tff(c_79, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_4])).
% 2.31/1.36  tff(c_255, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.36  tff(c_283, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_255])).
% 2.31/1.36  tff(c_305, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_283])).
% 2.31/1.36  tff(c_18, plain, (![C_16, A_14, B_15]: (k9_relat_1(C_16, k3_xboole_0(A_14, k10_relat_1(C_16, B_15)))=k3_xboole_0(k9_relat_1(C_16, A_14), B_15) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.36  tff(c_664, plain, (k3_xboole_0(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')), '#skF_2')=k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_305, c_18])).
% 2.31/1.36  tff(c_675, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_339, c_339, c_664])).
% 2.31/1.36  tff(c_8, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.36  tff(c_789, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_57, B_58), k3_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_8])).
% 2.31/1.36  tff(c_798, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_675, c_789])).
% 2.31/1.36  tff(c_850, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_798])).
% 2.31/1.36  tff(c_852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_850])).
% 2.31/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.36  
% 2.31/1.36  Inference rules
% 2.31/1.36  ----------------------
% 2.31/1.36  #Ref     : 0
% 2.31/1.36  #Sup     : 206
% 2.31/1.36  #Fact    : 0
% 2.31/1.36  #Define  : 0
% 2.31/1.36  #Split   : 0
% 2.31/1.36  #Chain   : 0
% 2.31/1.36  #Close   : 0
% 2.31/1.36  
% 2.31/1.36  Ordering : KBO
% 2.31/1.36  
% 2.31/1.36  Simplification rules
% 2.31/1.36  ----------------------
% 2.31/1.36  #Subsume      : 6
% 2.31/1.36  #Demod        : 144
% 2.31/1.36  #Tautology    : 145
% 2.31/1.36  #SimpNegUnit  : 1
% 2.31/1.36  #BackRed      : 0
% 2.31/1.36  
% 2.31/1.36  #Partial instantiations: 0
% 2.31/1.36  #Strategies tried      : 1
% 2.31/1.36  
% 2.31/1.36  Timing (in seconds)
% 2.31/1.36  ----------------------
% 2.31/1.36  Preprocessing        : 0.27
% 2.31/1.37  Parsing              : 0.15
% 2.31/1.37  CNF conversion       : 0.02
% 2.31/1.37  Main loop            : 0.29
% 2.31/1.37  Inferencing          : 0.12
% 2.31/1.37  Reduction            : 0.10
% 2.31/1.37  Demodulation         : 0.07
% 2.57/1.37  BG Simplification    : 0.01
% 2.57/1.37  Subsumption          : 0.04
% 2.57/1.37  Abstraction          : 0.02
% 2.57/1.37  MUC search           : 0.00
% 2.57/1.37  Cooper               : 0.00
% 2.57/1.37  Total                : 0.58
% 2.57/1.37  Index Insertion      : 0.00
% 2.57/1.37  Index Deletion       : 0.00
% 2.57/1.37  Index Matching       : 0.00
% 2.57/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
