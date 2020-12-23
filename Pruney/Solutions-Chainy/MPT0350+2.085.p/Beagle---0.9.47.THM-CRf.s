%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  76 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k3_subset_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_56,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_subset_1(A_20,B_21)) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_56])).

tff(c_93,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k3_subset_1(A_24,B_25),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_269,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,k3_subset_1(A_38,B_39)) = k3_subset_1(A_38,k3_subset_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_93,c_8])).

tff(c_273,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_269])).

tff(c_276,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_59,c_273])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_280,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_75])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_subset_1(A_30,B_31,C_32) = k2_xboole_0(B_31,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_442,plain,(
    ! [A_42,B_43,B_44] :
      ( k4_subset_1(A_42,B_43,k3_subset_1(A_42,B_44)) = k2_xboole_0(B_43,k3_subset_1(A_42,B_44))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_10,c_142])).

tff(c_452,plain,(
    ! [B_45] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_45)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_442])).

tff(c_459,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_452])).

tff(c_462,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_459])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.55  
% 2.69/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.55  %$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.69/1.55  
% 2.69/1.55  %Foreground sorts:
% 2.69/1.55  
% 2.69/1.55  
% 2.69/1.55  %Background operators:
% 2.69/1.55  
% 2.69/1.55  
% 2.69/1.55  %Foreground operators:
% 2.69/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.69/1.55  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.69/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.69/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.55  
% 2.69/1.57  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.69/1.57  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.69/1.57  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.69/1.57  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/1.57  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.69/1.57  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.69/1.57  tff(f_29, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.69/1.57  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.69/1.57  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.57  tff(c_16, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.57  tff(c_19, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.69/1.57  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.57  tff(c_64, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k3_subset_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.57  tff(c_68, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_64])).
% 2.69/1.57  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.57  tff(c_72, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_68, c_2])).
% 2.69/1.57  tff(c_56, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_subset_1(A_20, B_21))=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.57  tff(c_59, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_56])).
% 2.69/1.57  tff(c_93, plain, (![A_24, B_25]: (m1_subset_1(k3_subset_1(A_24, B_25), k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.57  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.57  tff(c_269, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_subset_1(A_38, B_39))=k3_subset_1(A_38, k3_subset_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(resolution, [status(thm)], [c_93, c_8])).
% 2.69/1.57  tff(c_273, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_269])).
% 2.69/1.57  tff(c_276, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_59, c_273])).
% 2.69/1.57  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.57  tff(c_75, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 2.69/1.57  tff(c_280, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_276, c_75])).
% 2.69/1.57  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.57  tff(c_142, plain, (![A_30, B_31, C_32]: (k4_subset_1(A_30, B_31, C_32)=k2_xboole_0(B_31, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.57  tff(c_442, plain, (![A_42, B_43, B_44]: (k4_subset_1(A_42, B_43, k3_subset_1(A_42, B_44))=k2_xboole_0(B_43, k3_subset_1(A_42, B_44)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_10, c_142])).
% 2.69/1.57  tff(c_452, plain, (![B_45]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_45))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_442])).
% 2.69/1.57  tff(c_459, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_452])).
% 2.69/1.57  tff(c_462, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_280, c_459])).
% 2.69/1.57  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_462])).
% 2.69/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.57  
% 2.69/1.57  Inference rules
% 2.69/1.57  ----------------------
% 2.69/1.57  #Ref     : 0
% 2.69/1.57  #Sup     : 124
% 2.69/1.57  #Fact    : 0
% 2.69/1.57  #Define  : 0
% 2.69/1.57  #Split   : 0
% 2.69/1.57  #Chain   : 0
% 2.69/1.57  #Close   : 0
% 2.69/1.57  
% 2.69/1.57  Ordering : KBO
% 2.69/1.57  
% 2.69/1.57  Simplification rules
% 2.69/1.57  ----------------------
% 2.69/1.57  #Subsume      : 1
% 2.69/1.57  #Demod        : 85
% 2.69/1.57  #Tautology    : 79
% 2.69/1.57  #SimpNegUnit  : 1
% 2.69/1.57  #BackRed      : 7
% 2.69/1.57  
% 2.69/1.57  #Partial instantiations: 0
% 2.69/1.57  #Strategies tried      : 1
% 2.69/1.57  
% 2.69/1.57  Timing (in seconds)
% 2.69/1.57  ----------------------
% 2.69/1.57  Preprocessing        : 0.34
% 2.69/1.57  Parsing              : 0.17
% 2.69/1.57  CNF conversion       : 0.02
% 2.69/1.57  Main loop            : 0.37
% 2.69/1.57  Inferencing          : 0.13
% 2.69/1.57  Reduction            : 0.13
% 2.69/1.57  Demodulation         : 0.10
% 2.69/1.57  BG Simplification    : 0.02
% 2.69/1.57  Subsumption          : 0.06
% 2.69/1.57  Abstraction          : 0.02
% 2.69/1.57  MUC search           : 0.00
% 2.69/1.57  Cooper               : 0.00
% 2.69/1.57  Total                : 0.75
% 2.69/1.57  Index Insertion      : 0.00
% 2.69/1.57  Index Deletion       : 0.00
% 2.69/1.57  Index Matching       : 0.00
% 2.69/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
