%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:41 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 122 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_10,plain,(
    ! [B_8] : k4_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) != k1_tarski(B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [B_8] : k1_tarski(B_8) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_90,plain,(
    ! [A_31,B_32] :
      ( k6_domain_1(A_31,B_32) = k1_tarski(B_32)
      | ~ m1_subset_1(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_96,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_93])).

tff(c_24,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_97,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_24])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k6_domain_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_166,plain,(
    ! [B_36,A_37] :
      ( ~ v1_subset_1(B_36,A_37)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_zfmisc_1(A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_184,plain,(
    ! [A_39,B_40] :
      ( ~ v1_subset_1(k6_domain_1(A_39,B_40),A_39)
      | v1_xboole_0(k6_domain_1(A_39,B_40))
      | ~ v1_zfmisc_1(A_39)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_187,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_184])).

tff(c_189,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_96,c_97,c_187])).

tff(c_190,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_189])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.26  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.26  
% 1.94/1.26  %Foreground sorts:
% 1.94/1.26  
% 1.94/1.26  
% 1.94/1.26  %Background operators:
% 1.94/1.26  
% 1.94/1.26  
% 1.94/1.26  %Foreground operators:
% 1.94/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.94/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.94/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.94/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.26  
% 1.94/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.94/1.27  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.94/1.27  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.94/1.27  tff(f_88, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.94/1.27  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.94/1.27  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.94/1.27  tff(f_76, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.94/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.27  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.27  tff(c_48, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.27  tff(c_55, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_48])).
% 1.94/1.27  tff(c_10, plain, (![B_8]: (k4_xboole_0(k1_tarski(B_8), k1_tarski(B_8))!=k1_tarski(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.27  tff(c_65, plain, (![B_8]: (k1_tarski(B_8)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_10])).
% 1.94/1.27  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.94/1.27  tff(c_26, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.94/1.27  tff(c_22, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.94/1.27  tff(c_90, plain, (![A_31, B_32]: (k6_domain_1(A_31, B_32)=k1_tarski(B_32) | ~m1_subset_1(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.27  tff(c_93, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_90])).
% 1.94/1.27  tff(c_96, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_93])).
% 1.94/1.27  tff(c_24, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.94/1.27  tff(c_97, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_24])).
% 1.94/1.27  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k6_domain_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.27  tff(c_166, plain, (![B_36, A_37]: (~v1_subset_1(B_36, A_37) | v1_xboole_0(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_zfmisc_1(A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.27  tff(c_184, plain, (![A_39, B_40]: (~v1_subset_1(k6_domain_1(A_39, B_40), A_39) | v1_xboole_0(k6_domain_1(A_39, B_40)) | ~v1_zfmisc_1(A_39) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_16, c_166])).
% 1.94/1.27  tff(c_187, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_184])).
% 1.94/1.27  tff(c_189, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_96, c_97, c_187])).
% 1.94/1.27  tff(c_190, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_189])).
% 1.94/1.27  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.27  tff(c_193, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_4])).
% 1.94/1.27  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_193])).
% 1.94/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.27  
% 1.94/1.27  Inference rules
% 1.94/1.27  ----------------------
% 1.94/1.27  #Ref     : 0
% 1.94/1.27  #Sup     : 35
% 1.94/1.27  #Fact    : 0
% 1.94/1.27  #Define  : 0
% 1.94/1.27  #Split   : 1
% 1.94/1.27  #Chain   : 0
% 1.94/1.27  #Close   : 0
% 1.94/1.27  
% 1.94/1.27  Ordering : KBO
% 1.94/1.27  
% 1.94/1.27  Simplification rules
% 1.94/1.27  ----------------------
% 1.94/1.27  #Subsume      : 2
% 1.94/1.27  #Demod        : 16
% 1.94/1.27  #Tautology    : 21
% 1.94/1.27  #SimpNegUnit  : 8
% 1.94/1.27  #BackRed      : 3
% 1.94/1.27  
% 1.94/1.27  #Partial instantiations: 0
% 1.94/1.27  #Strategies tried      : 1
% 1.94/1.27  
% 1.94/1.27  Timing (in seconds)
% 1.94/1.27  ----------------------
% 1.94/1.27  Preprocessing        : 0.32
% 1.94/1.27  Parsing              : 0.17
% 1.94/1.27  CNF conversion       : 0.02
% 1.94/1.27  Main loop            : 0.14
% 1.94/1.27  Inferencing          : 0.05
% 1.94/1.27  Reduction            : 0.04
% 1.94/1.27  Demodulation         : 0.03
% 1.94/1.27  BG Simplification    : 0.01
% 1.94/1.27  Subsumption          : 0.02
% 1.94/1.27  Abstraction          : 0.01
% 1.94/1.27  MUC search           : 0.00
% 1.94/1.27  Cooper               : 0.00
% 1.94/1.27  Total                : 0.48
% 1.94/1.27  Index Insertion      : 0.00
% 1.94/1.27  Index Deletion       : 0.00
% 1.94/1.27  Index Matching       : 0.00
% 1.94/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
