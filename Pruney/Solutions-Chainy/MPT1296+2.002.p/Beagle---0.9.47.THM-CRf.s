%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:40 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  76 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k8_setfam_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_58,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_4,C_22] : k7_subset_1(A_4,A_4,C_22) = k4_xboole_0(A_4,C_22) ),
    inference(resolution,[status(thm)],[c_23,c_58])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k7_subset_1(A_12,k2_subset_1(A_12),k6_setfam_1(A_12,B_13)) = k5_setfam_1(A_12,k7_setfam_1(A_12,B_13))
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( k7_subset_1(A_12,A_12,k6_setfam_1(A_12,B_13)) = k5_setfam_1(A_12,k7_setfam_1(A_12,B_13))
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_118,plain,(
    ! [A_30,B_31] :
      ( k5_setfam_1(A_30,k7_setfam_1(A_30,B_31)) = k4_xboole_0(A_30,k6_setfam_1(A_30,B_31))
      | k1_xboole_0 = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_123,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_130,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_123])).

tff(c_18,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_139,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_91,plain,(
    ! [A_28,B_29] :
      ( k8_setfam_1(A_28,B_29) = k6_setfam_1(A_28,B_29)
      | k1_xboole_0 = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_98,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_91])).

tff(c_106,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_98])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k8_setfam_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,
    ( m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14])).

tff(c_115,plain,(
    m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k3_subset_1(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:43:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  %$ m1_subset_1 > k7_subset_1 > k8_setfam_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.67/1.15  
% 1.67/1.15  %Foreground sorts:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Background operators:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Foreground operators:
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.15  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.67/1.15  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 1.67/1.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.67/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.15  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.67/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.15  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.15  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.15  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.67/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.15  
% 1.67/1.16  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 1.67/1.16  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.67/1.16  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.67/1.16  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.67/1.16  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_setfam_1)).
% 1.67/1.16  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 1.67/1.16  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 1.67/1.16  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.67/1.16  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.16  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.16  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.16  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.16  tff(c_23, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.67/1.16  tff(c_58, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.16  tff(c_64, plain, (![A_4, C_22]: (k7_subset_1(A_4, A_4, C_22)=k4_xboole_0(A_4, C_22))), inference(resolution, [status(thm)], [c_23, c_58])).
% 1.67/1.16  tff(c_16, plain, (![A_12, B_13]: (k7_subset_1(A_12, k2_subset_1(A_12), k6_setfam_1(A_12, B_13))=k5_setfam_1(A_12, k7_setfam_1(A_12, B_13)) | k1_xboole_0=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.67/1.16  tff(c_24, plain, (![A_12, B_13]: (k7_subset_1(A_12, A_12, k6_setfam_1(A_12, B_13))=k5_setfam_1(A_12, k7_setfam_1(A_12, B_13)) | k1_xboole_0=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.67/1.16  tff(c_118, plain, (![A_30, B_31]: (k5_setfam_1(A_30, k7_setfam_1(A_30, B_31))=k4_xboole_0(A_30, k6_setfam_1(A_30, B_31)) | k1_xboole_0=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 1.67/1.16  tff(c_123, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_22, c_118])).
% 1.67/1.16  tff(c_130, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_20, c_123])).
% 1.67/1.16  tff(c_18, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.16  tff(c_139, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_18])).
% 1.67/1.16  tff(c_91, plain, (![A_28, B_29]: (k8_setfam_1(A_28, B_29)=k6_setfam_1(A_28, B_29) | k1_xboole_0=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.16  tff(c_98, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_22, c_91])).
% 1.67/1.16  tff(c_106, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_98])).
% 1.67/1.16  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k8_setfam_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.67/1.16  tff(c_111, plain, (m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_14])).
% 1.67/1.16  tff(c_115, plain, (m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_111])).
% 1.67/1.16  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k3_subset_1(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.16  tff(c_138, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_115, c_4])).
% 1.67/1.16  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_138])).
% 1.67/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  Inference rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Ref     : 0
% 1.67/1.16  #Sup     : 29
% 1.67/1.16  #Fact    : 0
% 1.67/1.16  #Define  : 0
% 1.67/1.16  #Split   : 0
% 1.67/1.16  #Chain   : 0
% 1.67/1.16  #Close   : 0
% 1.67/1.16  
% 1.67/1.16  Ordering : KBO
% 1.67/1.16  
% 1.67/1.16  Simplification rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Subsume      : 0
% 1.67/1.16  #Demod        : 5
% 1.67/1.16  #Tautology    : 14
% 1.67/1.16  #SimpNegUnit  : 3
% 1.67/1.16  #BackRed      : 1
% 1.67/1.16  
% 1.67/1.16  #Partial instantiations: 0
% 1.67/1.16  #Strategies tried      : 1
% 1.67/1.16  
% 1.67/1.16  Timing (in seconds)
% 1.67/1.16  ----------------------
% 1.67/1.17  Preprocessing        : 0.29
% 1.67/1.17  Parsing              : 0.15
% 1.67/1.17  CNF conversion       : 0.02
% 1.67/1.17  Main loop            : 0.13
% 1.67/1.17  Inferencing          : 0.04
% 1.67/1.17  Reduction            : 0.04
% 1.67/1.17  Demodulation         : 0.03
% 1.67/1.17  BG Simplification    : 0.01
% 1.67/1.17  Subsumption          : 0.02
% 1.67/1.17  Abstraction          : 0.01
% 1.67/1.17  MUC search           : 0.00
% 1.67/1.17  Cooper               : 0.00
% 1.67/1.17  Total                : 0.44
% 1.67/1.17  Index Insertion      : 0.00
% 1.67/1.17  Index Deletion       : 0.00
% 1.67/1.17  Index Matching       : 0.00
% 1.67/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
