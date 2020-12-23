%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 194 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_396,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,k9_relat_1(B_44,k1_relat_1(B_44))) = k9_relat_1(B_44,k10_relat_1(B_44,A_43))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_446,plain,(
    ! [A_8,A_43] :
      ( k9_relat_1(A_8,k10_relat_1(A_8,A_43)) = k3_xboole_0(A_43,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_396])).

tff(c_18,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_283,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_122,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,k10_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_23,k10_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_146,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_tarski(k9_relat_1(C_27,A_28),k9_relat_1(C_27,B_29))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4979,plain,(
    ! [C_127,A_128,B_129] :
      ( k3_xboole_0(k9_relat_1(C_127,A_128),k9_relat_1(C_127,B_129)) = k9_relat_1(C_127,A_128)
      | ~ r1_tarski(A_128,B_129)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_146,c_6])).

tff(c_5109,plain,(
    ! [C_130,A_131,B_132] :
      ( r1_tarski(k9_relat_1(C_130,A_131),k9_relat_1(C_130,A_131))
      | ~ r1_tarski(A_131,B_132)
      | ~ v1_relat_1(C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4979,c_2])).

tff(c_5217,plain,(
    ! [C_134] :
      ( r1_tarski(k9_relat_1(C_134,k10_relat_1('#skF_3','#skF_1')),k9_relat_1(C_134,k10_relat_1('#skF_3','#skF_1')))
      | ~ v1_relat_1(C_134) ) ),
    inference(resolution,[status(thm)],[c_18,c_5109])).

tff(c_5234,plain,
    ( r1_tarski(k3_xboole_0('#skF_1',k2_relat_1('#skF_3')),k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_5217])).

tff(c_5246,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_20,c_22,c_32,c_5234])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_3,C_27,B_29,A_28] :
      ( r1_tarski(A_3,k9_relat_1(C_27,B_29))
      | ~ r1_tarski(A_3,k9_relat_1(C_27,A_28))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_5252,plain,(
    ! [B_29] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_29))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_29)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5246,c_158])).

tff(c_5432,plain,(
    ! [B_135] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_135))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5252])).

tff(c_5456,plain,
    ( r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_134,c_5432])).

tff(c_5480,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_5456])).

tff(c_5636,plain,
    ( r1_tarski('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_5480])).

tff(c_5647,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_20,c_5636])).

tff(c_136,plain,(
    ! [A_23,A_1,B_2] :
      ( r1_tarski(A_23,A_1)
      | ~ r1_tarski(A_23,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2,c_122])).

tff(c_5659,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5647,c_136])).

tff(c_5680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_5659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.08  
% 5.18/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.08  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.18/2.08  
% 5.18/2.08  %Foreground sorts:
% 5.18/2.08  
% 5.18/2.08  
% 5.18/2.08  %Background operators:
% 5.18/2.08  
% 5.18/2.08  
% 5.18/2.08  %Foreground operators:
% 5.18/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.18/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.18/2.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.18/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.18/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.18/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.18/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.18/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.18/2.09  
% 5.30/2.10  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 5.30/2.10  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.30/2.10  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 5.30/2.10  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.30/2.10  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.30/2.10  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.30/2.10  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 5.30/2.10  tff(c_14, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.30/2.10  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.30/2.10  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.30/2.10  tff(c_8, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.30/2.10  tff(c_396, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k9_relat_1(B_44, k1_relat_1(B_44)))=k9_relat_1(B_44, k10_relat_1(B_44, A_43)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.30/2.10  tff(c_446, plain, (![A_8, A_43]: (k9_relat_1(A_8, k10_relat_1(A_8, A_43))=k3_xboole_0(A_43, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_396])).
% 5.30/2.10  tff(c_18, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.30/2.10  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.30/2.10  tff(c_55, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_6])).
% 5.30/2.10  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.30/2.10  tff(c_283, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 5.30/2.10  tff(c_122, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.30/2.10  tff(c_134, plain, (![A_23]: (r1_tarski(A_23, k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_23, k10_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_18, c_122])).
% 5.30/2.10  tff(c_16, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.30/2.10  tff(c_24, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.30/2.10  tff(c_32, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_16, c_24])).
% 5.30/2.10  tff(c_146, plain, (![C_27, A_28, B_29]: (r1_tarski(k9_relat_1(C_27, A_28), k9_relat_1(C_27, B_29)) | ~r1_tarski(A_28, B_29) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.30/2.10  tff(c_4979, plain, (![C_127, A_128, B_129]: (k3_xboole_0(k9_relat_1(C_127, A_128), k9_relat_1(C_127, B_129))=k9_relat_1(C_127, A_128) | ~r1_tarski(A_128, B_129) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_146, c_6])).
% 5.30/2.10  tff(c_5109, plain, (![C_130, A_131, B_132]: (r1_tarski(k9_relat_1(C_130, A_131), k9_relat_1(C_130, A_131)) | ~r1_tarski(A_131, B_132) | ~v1_relat_1(C_130))), inference(superposition, [status(thm), theory('equality')], [c_4979, c_2])).
% 5.30/2.10  tff(c_5217, plain, (![C_134]: (r1_tarski(k9_relat_1(C_134, k10_relat_1('#skF_3', '#skF_1')), k9_relat_1(C_134, k10_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(C_134))), inference(resolution, [status(thm)], [c_18, c_5109])).
% 5.30/2.10  tff(c_5234, plain, (r1_tarski(k3_xboole_0('#skF_1', k2_relat_1('#skF_3')), k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_446, c_5217])).
% 5.30/2.10  tff(c_5246, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_20, c_22, c_32, c_5234])).
% 5.30/2.10  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.30/2.10  tff(c_158, plain, (![A_3, C_27, B_29, A_28]: (r1_tarski(A_3, k9_relat_1(C_27, B_29)) | ~r1_tarski(A_3, k9_relat_1(C_27, A_28)) | ~r1_tarski(A_28, B_29) | ~v1_relat_1(C_27))), inference(resolution, [status(thm)], [c_146, c_4])).
% 5.30/2.10  tff(c_5252, plain, (![B_29]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_29)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_29) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5246, c_158])).
% 5.30/2.10  tff(c_5432, plain, (![B_135]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_135)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_135))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5252])).
% 5.30/2.10  tff(c_5456, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_134, c_5432])).
% 5.30/2.10  tff(c_5480, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_5456])).
% 5.30/2.10  tff(c_5636, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_446, c_5480])).
% 5.30/2.10  tff(c_5647, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_20, c_5636])).
% 5.30/2.10  tff(c_136, plain, (![A_23, A_1, B_2]: (r1_tarski(A_23, A_1) | ~r1_tarski(A_23, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_122])).
% 5.30/2.10  tff(c_5659, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5647, c_136])).
% 5.30/2.10  tff(c_5680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_5659])).
% 5.30/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.10  
% 5.30/2.10  Inference rules
% 5.30/2.10  ----------------------
% 5.30/2.10  #Ref     : 0
% 5.30/2.10  #Sup     : 1384
% 5.30/2.10  #Fact    : 0
% 5.30/2.10  #Define  : 0
% 5.30/2.10  #Split   : 2
% 5.30/2.10  #Chain   : 0
% 5.30/2.10  #Close   : 0
% 5.30/2.10  
% 5.30/2.10  Ordering : KBO
% 5.30/2.10  
% 5.30/2.10  Simplification rules
% 5.30/2.10  ----------------------
% 5.30/2.10  #Subsume      : 406
% 5.30/2.10  #Demod        : 917
% 5.30/2.10  #Tautology    : 597
% 5.30/2.10  #SimpNegUnit  : 1
% 5.30/2.10  #BackRed      : 0
% 5.30/2.10  
% 5.30/2.10  #Partial instantiations: 0
% 5.30/2.10  #Strategies tried      : 1
% 5.30/2.10  
% 5.30/2.10  Timing (in seconds)
% 5.30/2.10  ----------------------
% 5.30/2.10  Preprocessing        : 0.33
% 5.30/2.10  Parsing              : 0.19
% 5.30/2.10  CNF conversion       : 0.02
% 5.30/2.10  Main loop            : 0.95
% 5.30/2.10  Inferencing          : 0.32
% 5.30/2.10  Reduction            : 0.33
% 5.30/2.10  Demodulation         : 0.25
% 5.30/2.10  BG Simplification    : 0.03
% 5.30/2.10  Subsumption          : 0.21
% 5.30/2.10  Abstraction          : 0.05
% 5.30/2.10  MUC search           : 0.00
% 5.30/2.10  Cooper               : 0.00
% 5.30/2.10  Total                : 1.31
% 5.30/2.10  Index Insertion      : 0.00
% 5.30/2.10  Index Deletion       : 0.00
% 5.30/2.10  Index Matching       : 0.00
% 5.30/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
