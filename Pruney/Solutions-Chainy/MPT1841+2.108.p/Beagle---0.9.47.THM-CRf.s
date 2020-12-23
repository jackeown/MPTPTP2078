%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:42 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 112 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [C_41,B_42] : k4_xboole_0(k1_tarski(C_41),k2_tarski(B_42,C_41)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    ! [A_6] : k4_xboole_0(k1_tarski(A_6),k1_tarski(A_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_14,plain,(
    ! [B_13] : k4_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) != k1_tarski(B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_14])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_216,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(A_59,B_60) = k1_tarski(B_60)
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_219,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_216])).

tff(c_222,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_219])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_223,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_40])).

tff(c_228,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k6_domain_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_237,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_228])).

tff(c_241,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_237])).

tff(c_242,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_241])).

tff(c_368,plain,(
    ! [B_70,A_71] :
      ( ~ v1_subset_1(B_70,A_71)
      | v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_374,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_368])).

tff(c_383,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_223,c_374])).

tff(c_384,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_383])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_388,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:37:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  
% 2.26/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.26/1.25  
% 2.26/1.25  %Foreground sorts:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Background operators:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Foreground operators:
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.26/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.26/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.26/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.26/1.25  
% 2.26/1.26  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.26  tff(f_59, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.26/1.26  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.26/1.26  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.26/1.26  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.26/1.26  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.26/1.26  tff(f_97, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.26/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.26/1.26  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.26  tff(c_111, plain, (![C_41, B_42]: (k4_xboole_0(k1_tarski(C_41), k2_tarski(B_42, C_41))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.26  tff(c_118, plain, (![A_6]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(A_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 2.26/1.26  tff(c_14, plain, (![B_13]: (k4_xboole_0(k1_tarski(B_13), k1_tarski(B_13))!=k1_tarski(B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.26  tff(c_147, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_14])).
% 2.26/1.26  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.26  tff(c_38, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.26  tff(c_42, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.26  tff(c_216, plain, (![A_59, B_60]: (k6_domain_1(A_59, B_60)=k1_tarski(B_60) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.26  tff(c_219, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_216])).
% 2.26/1.26  tff(c_222, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_219])).
% 2.26/1.26  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.26  tff(c_223, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_40])).
% 2.26/1.26  tff(c_228, plain, (![A_61, B_62]: (m1_subset_1(k6_domain_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.26/1.26  tff(c_237, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_222, c_228])).
% 2.26/1.26  tff(c_241, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_237])).
% 2.26/1.26  tff(c_242, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_241])).
% 2.26/1.26  tff(c_368, plain, (![B_70, A_71]: (~v1_subset_1(B_70, A_71) | v1_xboole_0(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_374, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_242, c_368])).
% 2.26/1.26  tff(c_383, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_223, c_374])).
% 2.26/1.26  tff(c_384, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_383])).
% 2.26/1.26  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.26  tff(c_388, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_384, c_4])).
% 2.26/1.26  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_388])).
% 2.26/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  Inference rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Ref     : 0
% 2.26/1.26  #Sup     : 76
% 2.26/1.26  #Fact    : 0
% 2.26/1.26  #Define  : 0
% 2.26/1.26  #Split   : 1
% 2.26/1.26  #Chain   : 0
% 2.26/1.26  #Close   : 0
% 2.26/1.26  
% 2.26/1.26  Ordering : KBO
% 2.26/1.26  
% 2.26/1.26  Simplification rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Subsume      : 3
% 2.26/1.26  #Demod        : 22
% 2.26/1.26  #Tautology    : 52
% 2.26/1.26  #SimpNegUnit  : 14
% 2.26/1.26  #BackRed      : 3
% 2.26/1.26  
% 2.26/1.26  #Partial instantiations: 0
% 2.26/1.26  #Strategies tried      : 1
% 2.26/1.26  
% 2.26/1.26  Timing (in seconds)
% 2.26/1.26  ----------------------
% 2.26/1.27  Preprocessing        : 0.31
% 2.26/1.27  Parsing              : 0.16
% 2.26/1.27  CNF conversion       : 0.02
% 2.26/1.27  Main loop            : 0.21
% 2.26/1.27  Inferencing          : 0.08
% 2.26/1.27  Reduction            : 0.07
% 2.26/1.27  Demodulation         : 0.05
% 2.26/1.27  BG Simplification    : 0.01
% 2.26/1.27  Subsumption          : 0.04
% 2.26/1.27  Abstraction          : 0.01
% 2.26/1.27  MUC search           : 0.00
% 2.26/1.27  Cooper               : 0.00
% 2.26/1.27  Total                : 0.54
% 2.26/1.27  Index Insertion      : 0.00
% 2.26/1.27  Index Deletion       : 0.00
% 2.26/1.27  Index Matching       : 0.00
% 2.26/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
