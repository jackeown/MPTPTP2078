%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k6_setfam_1(A_23,B_24),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k3_subset_1(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,k6_setfam_1(A_25,B_26)) = k3_subset_1(A_25,k6_setfam_1(A_25,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_96,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_53,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_4,C_19] : k7_subset_1(A_4,A_4,C_19) = k4_xboole_0(A_4,C_19) ),
    inference(resolution,[status(thm)],[c_19,c_53])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k7_subset_1(A_10,k2_subset_1(A_10),k6_setfam_1(A_10,B_11)) = k5_setfam_1(A_10,k7_setfam_1(A_10,B_11))
      | k1_xboole_0 = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( k7_subset_1(A_10,A_10,k6_setfam_1(A_10,B_11)) = k5_setfam_1(A_10,k7_setfam_1(A_10,B_11))
      | k1_xboole_0 = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_112,plain,(
    ! [A_28,B_29] :
      ( k5_setfam_1(A_28,k7_setfam_1(A_28,B_29)) = k4_xboole_0(A_28,k6_setfam_1(A_28,B_29))
      | k1_xboole_0 = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_20])).

tff(c_117,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_112])).

tff(c_123,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_117])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_14,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:55:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  %$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.24  
% 1.97/1.24  %Foreground sorts:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Background operators:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Foreground operators:
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.24  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.97/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.97/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.24  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.97/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.24  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.24  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.24  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.97/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.24  
% 1.97/1.25  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 1.97/1.25  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 1.97/1.25  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.97/1.25  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.97/1.25  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.97/1.25  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.97/1.25  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 1.97/1.25  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.25  tff(c_14, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.25  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.25  tff(c_78, plain, (![A_23, B_24]: (m1_subset_1(k6_setfam_1(A_23, B_24), k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.25  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k3_subset_1(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.25  tff(c_86, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k6_setfam_1(A_25, B_26))=k3_subset_1(A_25, k6_setfam_1(A_25, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(resolution, [status(thm)], [c_78, c_4])).
% 1.97/1.25  tff(c_96, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_86])).
% 1.97/1.25  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.25  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.25  tff(c_19, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.97/1.25  tff(c_53, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.25  tff(c_59, plain, (![A_4, C_19]: (k7_subset_1(A_4, A_4, C_19)=k4_xboole_0(A_4, C_19))), inference(resolution, [status(thm)], [c_19, c_53])).
% 1.97/1.25  tff(c_12, plain, (![A_10, B_11]: (k7_subset_1(A_10, k2_subset_1(A_10), k6_setfam_1(A_10, B_11))=k5_setfam_1(A_10, k7_setfam_1(A_10, B_11)) | k1_xboole_0=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.25  tff(c_20, plain, (![A_10, B_11]: (k7_subset_1(A_10, A_10, k6_setfam_1(A_10, B_11))=k5_setfam_1(A_10, k7_setfam_1(A_10, B_11)) | k1_xboole_0=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.97/1.25  tff(c_112, plain, (![A_28, B_29]: (k5_setfam_1(A_28, k7_setfam_1(A_28, B_29))=k4_xboole_0(A_28, k6_setfam_1(A_28, B_29)) | k1_xboole_0=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_20])).
% 1.97/1.25  tff(c_117, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_18, c_112])).
% 1.97/1.25  tff(c_123, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_117])).
% 1.97/1.25  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_14, c_123])).
% 1.97/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  Inference rules
% 1.97/1.25  ----------------------
% 1.97/1.25  #Ref     : 0
% 1.97/1.25  #Sup     : 26
% 1.97/1.25  #Fact    : 0
% 1.97/1.25  #Define  : 0
% 1.97/1.25  #Split   : 0
% 1.97/1.25  #Chain   : 0
% 1.97/1.25  #Close   : 0
% 1.97/1.25  
% 1.97/1.25  Ordering : KBO
% 1.97/1.25  
% 1.97/1.25  Simplification rules
% 1.97/1.25  ----------------------
% 1.97/1.25  #Subsume      : 0
% 1.97/1.25  #Demod        : 4
% 1.97/1.25  #Tautology    : 14
% 1.97/1.25  #SimpNegUnit  : 1
% 1.97/1.25  #BackRed      : 0
% 1.97/1.25  
% 1.97/1.25  #Partial instantiations: 0
% 1.97/1.25  #Strategies tried      : 1
% 1.97/1.25  
% 1.97/1.25  Timing (in seconds)
% 1.97/1.25  ----------------------
% 1.97/1.25  Preprocessing        : 0.33
% 1.97/1.25  Parsing              : 0.19
% 1.97/1.25  CNF conversion       : 0.02
% 1.97/1.25  Main loop            : 0.15
% 1.97/1.25  Inferencing          : 0.06
% 1.97/1.25  Reduction            : 0.05
% 1.97/1.25  Demodulation         : 0.03
% 1.97/1.25  BG Simplification    : 0.01
% 1.97/1.25  Subsumption          : 0.02
% 1.97/1.25  Abstraction          : 0.01
% 1.97/1.25  MUC search           : 0.00
% 1.97/1.25  Cooper               : 0.00
% 1.97/1.25  Total                : 0.52
% 1.97/1.25  Index Insertion      : 0.00
% 1.97/1.25  Index Deletion       : 0.00
% 1.97/1.25  Index Matching       : 0.00
% 1.97/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
