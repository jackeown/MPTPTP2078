%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:29 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 121 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_49,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(c_16,plain,(
    ! [A_12] : k1_ordinal1(A_12) != A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    ! [A_33,B_34] :
      ( k6_domain_1(A_33,B_34) = k1_tarski(B_34)
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_105,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_102])).

tff(c_26,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_106,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_26])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k6_domain_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,(
    ! [B_38,A_39] :
      ( ~ v1_subset_1(B_38,A_39)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_zfmisc_1(A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_184,plain,(
    ! [A_40,B_41] :
      ( ~ v1_subset_1(k6_domain_1(A_40,B_41),A_40)
      | v1_xboole_0(k6_domain_1(A_40,B_41))
      | ~ v1_zfmisc_1(A_40)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_18,c_173])).

tff(c_187,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_184])).

tff(c_189,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_105,c_106,c_187])).

tff(c_190,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_189])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_194,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_2])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_tarski(A_11)) = k1_ordinal1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_206,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_ordinal1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_14])).

tff(c_209,plain,(
    k1_ordinal1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_206])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.33  
% 2.23/1.33  %Foreground sorts:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Background operators:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Foreground operators:
% 2.23/1.33  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.23/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.23/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.23/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.33  
% 2.23/1.34  tff(f_49, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.23/1.34  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.23/1.34  tff(f_89, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.23/1.34  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.23/1.34  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.23/1.34  tff(f_77, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.23/1.34  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.34  tff(f_46, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.23/1.34  tff(c_16, plain, (![A_12]: (k1_ordinal1(A_12)!=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.34  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.34  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.23/1.34  tff(c_28, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.23/1.34  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.23/1.34  tff(c_99, plain, (![A_33, B_34]: (k6_domain_1(A_33, B_34)=k1_tarski(B_34) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.23/1.34  tff(c_102, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.23/1.34  tff(c_105, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_102])).
% 2.23/1.34  tff(c_26, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.23/1.34  tff(c_106, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_26])).
% 2.23/1.34  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k6_domain_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.34  tff(c_173, plain, (![B_38, A_39]: (~v1_subset_1(B_38, A_39) | v1_xboole_0(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_zfmisc_1(A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.34  tff(c_184, plain, (![A_40, B_41]: (~v1_subset_1(k6_domain_1(A_40, B_41), A_40) | v1_xboole_0(k6_domain_1(A_40, B_41)) | ~v1_zfmisc_1(A_40) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_18, c_173])).
% 2.23/1.34  tff(c_187, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_184])).
% 2.23/1.34  tff(c_189, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_105, c_106, c_187])).
% 2.23/1.34  tff(c_190, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_189])).
% 2.23/1.34  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.34  tff(c_194, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_2])).
% 2.23/1.34  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_tarski(A_11))=k1_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.34  tff(c_206, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_ordinal1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_14])).
% 2.23/1.34  tff(c_209, plain, (k1_ordinal1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_206])).
% 2.23/1.34  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_209])).
% 2.23/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  Inference rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Ref     : 0
% 2.23/1.35  #Sup     : 40
% 2.23/1.35  #Fact    : 0
% 2.23/1.35  #Define  : 0
% 2.23/1.35  #Split   : 1
% 2.23/1.35  #Chain   : 0
% 2.23/1.35  #Close   : 0
% 2.23/1.35  
% 2.23/1.35  Ordering : KBO
% 2.23/1.35  
% 2.23/1.35  Simplification rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Subsume      : 2
% 2.23/1.35  #Demod        : 19
% 2.23/1.35  #Tautology    : 25
% 2.23/1.35  #SimpNegUnit  : 6
% 2.23/1.35  #BackRed      : 7
% 2.23/1.35  
% 2.23/1.35  #Partial instantiations: 0
% 2.23/1.35  #Strategies tried      : 1
% 2.23/1.35  
% 2.23/1.35  Timing (in seconds)
% 2.23/1.35  ----------------------
% 2.23/1.35  Preprocessing        : 0.38
% 2.23/1.35  Parsing              : 0.20
% 2.23/1.35  CNF conversion       : 0.02
% 2.23/1.35  Main loop            : 0.18
% 2.23/1.35  Inferencing          : 0.07
% 2.23/1.35  Reduction            : 0.06
% 2.23/1.35  Demodulation         : 0.03
% 2.23/1.35  BG Simplification    : 0.01
% 2.23/1.35  Subsumption          : 0.03
% 2.23/1.35  Abstraction          : 0.01
% 2.23/1.35  MUC search           : 0.00
% 2.23/1.35  Cooper               : 0.00
% 2.23/1.35  Total                : 0.58
% 2.23/1.35  Index Insertion      : 0.00
% 2.23/1.35  Index Deletion       : 0.00
% 2.23/1.35  Index Matching       : 0.00
% 2.23/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
