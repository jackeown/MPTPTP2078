%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:30 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 (  66 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 110 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_49,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_97,plain,(
    ! [A_38,B_39] :
      ( k6_domain_1(A_38,B_39) = k1_tarski(B_39)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_100,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_103,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_100])).

tff(c_26,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_104,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_26])).

tff(c_109,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k6_domain_1(A_40,B_41),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_109])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_118])).

tff(c_123,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_122])).

tff(c_218,plain,(
    ! [B_46,A_47] :
      ( ~ v1_subset_1(B_46,A_47)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_224,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_123,c_218])).

tff(c_233,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_104,c_224])).

tff(c_234,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_233])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_55,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_238,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_234,c_58])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.03/1.25  
% 2.03/1.25  %Foreground sorts:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Background operators:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Foreground operators:
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.03/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.03/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.03/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.25  
% 2.03/1.26  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.03/1.26  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.03/1.26  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.03/1.26  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.03/1.26  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.03/1.26  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.03/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.03/1.26  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.03/1.26  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.03/1.26  tff(c_49, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.26  tff(c_53, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_49])).
% 2.03/1.26  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.26  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.26  tff(c_28, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.26  tff(c_97, plain, (![A_38, B_39]: (k6_domain_1(A_38, B_39)=k1_tarski(B_39) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.03/1.26  tff(c_100, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_97])).
% 2.03/1.26  tff(c_103, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_100])).
% 2.03/1.26  tff(c_26, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.26  tff(c_104, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_26])).
% 2.03/1.26  tff(c_109, plain, (![A_40, B_41]: (m1_subset_1(k6_domain_1(A_40, B_41), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.26  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103, c_109])).
% 2.03/1.26  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_118])).
% 2.03/1.26  tff(c_123, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_30, c_122])).
% 2.03/1.26  tff(c_218, plain, (![B_46, A_47]: (~v1_subset_1(B_46, A_47) | v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.26  tff(c_224, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_123, c_218])).
% 2.03/1.26  tff(c_233, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_104, c_224])).
% 2.03/1.26  tff(c_234, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_233])).
% 2.03/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.03/1.26  tff(c_55, plain, (![B_28, A_29]: (~v1_xboole_0(B_28) | B_28=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.03/1.26  tff(c_58, plain, (![A_29]: (k1_xboole_0=A_29 | ~v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_2, c_55])).
% 2.03/1.26  tff(c_238, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_234, c_58])).
% 2.03/1.26  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_238])).
% 2.03/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  Inference rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Ref     : 0
% 2.03/1.26  #Sup     : 46
% 2.03/1.26  #Fact    : 0
% 2.03/1.26  #Define  : 0
% 2.03/1.26  #Split   : 1
% 2.03/1.26  #Chain   : 0
% 2.03/1.26  #Close   : 0
% 2.03/1.26  
% 2.03/1.26  Ordering : KBO
% 2.03/1.26  
% 2.03/1.26  Simplification rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Subsume      : 4
% 2.03/1.26  #Demod        : 16
% 2.03/1.26  #Tautology    : 22
% 2.03/1.26  #SimpNegUnit  : 9
% 2.03/1.26  #BackRed      : 3
% 2.03/1.26  
% 2.03/1.26  #Partial instantiations: 0
% 2.03/1.26  #Strategies tried      : 1
% 2.03/1.26  
% 2.03/1.26  Timing (in seconds)
% 2.03/1.26  ----------------------
% 2.03/1.27  Preprocessing        : 0.28
% 2.03/1.27  Parsing              : 0.15
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.18
% 2.03/1.27  Inferencing          : 0.07
% 2.03/1.27  Reduction            : 0.05
% 2.03/1.27  Demodulation         : 0.04
% 2.03/1.27  BG Simplification    : 0.01
% 2.03/1.27  Subsumption          : 0.03
% 2.03/1.27  Abstraction          : 0.01
% 2.03/1.27  MUC search           : 0.00
% 2.03/1.27  Cooper               : 0.00
% 2.03/1.27  Total                : 0.49
% 2.03/1.27  Index Insertion      : 0.00
% 2.03/1.27  Index Deletion       : 0.00
% 2.03/1.27  Index Matching       : 0.00
% 2.03/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
