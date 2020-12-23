%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:06 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 140 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 ( 337 expanded)
%              Number of equality atoms :   17 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_19,plain,(
    ! [C_10,A_11,B_12] :
      ( k3_partfun1(C_10,A_11,B_12) = C_10
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,
    ( k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_25,plain,(
    k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_12,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_27,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_12])).

tff(c_39,plain,(
    ! [A_18,B_19,C_20] :
      ( k5_partfun1(A_18,B_19,C_20) = k1_tarski(C_20)
      | ~ v1_partfun1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_45,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42])).

tff(c_46,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_45])).

tff(c_16,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_47,plain,(
    ! [B_21,C_22,A_23] :
      ( k1_xboole_0 = B_21
      | v1_partfun1(C_22,A_23)
      | ~ v1_funct_2(C_22,A_23,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_21)))
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_53,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_50])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_53])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(C_3,k1_xboole_0)
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [C_24,B_25] :
      ( v1_partfun1(C_24,'#skF_1')
      | ~ v1_funct_2(C_24,'#skF_1',B_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_25)))
      | ~ v1_funct_1(C_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_54,c_2])).

tff(c_64,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_61])).

tff(c_67,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_64])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.81/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.81/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.81/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.21  
% 1.87/1.22  tff(f_65, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_2)).
% 1.87/1.22  tff(f_56, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 1.87/1.22  tff(f_50, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 1.87/1.22  tff(f_42, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.87/1.22  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.22  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.22  tff(c_19, plain, (![C_10, A_11, B_12]: (k3_partfun1(C_10, A_11, B_12)=C_10 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.22  tff(c_22, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.87/1.22  tff(c_25, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 1.87/1.22  tff(c_12, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.22  tff(c_27, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25, c_12])).
% 1.87/1.22  tff(c_39, plain, (![A_18, B_19, C_20]: (k5_partfun1(A_18, B_19, C_20)=k1_tarski(C_20) | ~v1_partfun1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.22  tff(c_42, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_39])).
% 1.87/1.22  tff(c_45, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42])).
% 1.87/1.22  tff(c_46, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_27, c_45])).
% 1.87/1.22  tff(c_16, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.22  tff(c_47, plain, (![B_21, C_22, A_23]: (k1_xboole_0=B_21 | v1_partfun1(C_22, A_23) | ~v1_funct_2(C_22, A_23, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_21))) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.22  tff(c_50, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_47])).
% 1.87/1.22  tff(c_53, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_50])).
% 1.87/1.22  tff(c_54, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_46, c_53])).
% 1.87/1.22  tff(c_2, plain, (![C_3, B_2]: (v1_partfun1(C_3, k1_xboole_0) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.22  tff(c_61, plain, (![C_24, B_25]: (v1_partfun1(C_24, '#skF_1') | ~v1_funct_2(C_24, '#skF_1', B_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_25))) | ~v1_funct_1(C_24))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_54, c_2])).
% 1.87/1.22  tff(c_64, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_61])).
% 1.87/1.22  tff(c_67, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_64])).
% 1.87/1.22  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_67])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 0
% 1.87/1.22  #Sup     : 9
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 0
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 1
% 1.87/1.22  #Demod        : 12
% 1.87/1.22  #Tautology    : 4
% 1.87/1.22  #SimpNegUnit  : 3
% 1.87/1.22  #BackRed      : 3
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.22  Preprocessing        : 0.31
% 1.87/1.22  Parsing              : 0.16
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.09
% 1.87/1.22  Inferencing          : 0.03
% 1.87/1.22  Reduction            : 0.03
% 1.87/1.22  Demodulation         : 0.02
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.01
% 1.87/1.22  Abstraction          : 0.01
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.22  Cooper               : 0.00
% 1.87/1.22  Total                : 0.42
% 1.87/1.22  Index Insertion      : 0.00
% 1.87/1.22  Index Deletion       : 0.00
% 1.87/1.22  Index Matching       : 0.00
% 1.87/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
