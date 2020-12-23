%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:42 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 111 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
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
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_84,axiom,(
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

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_107,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_104])).

tff(c_16,plain,(
    ! [B_14] : k4_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_tarski(B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_16])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_149,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_155,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_152])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_156,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_32])).

tff(c_161,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_161])).

tff(c_174,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_170])).

tff(c_175,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_174])).

tff(c_191,plain,(
    ! [B_53,A_54] :
      ( ~ v1_subset_1(B_53,A_54)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_194,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_191])).

tff(c_200,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_156,c_194])).

tff(c_201,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_200])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_4])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.15  
% 1.91/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.15  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.91/1.15  
% 1.91/1.15  %Foreground sorts:
% 1.91/1.15  
% 1.91/1.15  
% 1.91/1.15  %Background operators:
% 1.91/1.15  
% 1.91/1.15  
% 1.91/1.15  %Foreground operators:
% 1.91/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.15  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.91/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.15  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.91/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.15  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.91/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.15  
% 1.91/1.16  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.91/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.91/1.16  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.91/1.16  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.91/1.16  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.91/1.16  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.91/1.16  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.91/1.16  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.91/1.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.91/1.16  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.16  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.16  tff(c_95, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.16  tff(c_104, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 1.91/1.16  tff(c_107, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_104])).
% 1.91/1.16  tff(c_16, plain, (![B_14]: (k4_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_tarski(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.16  tff(c_108, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_16])).
% 1.91/1.16  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.91/1.16  tff(c_30, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.91/1.16  tff(c_34, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.91/1.16  tff(c_149, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.16  tff(c_152, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_149])).
% 1.91/1.16  tff(c_155, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_152])).
% 1.91/1.16  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.91/1.16  tff(c_156, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_32])).
% 1.91/1.16  tff(c_161, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.16  tff(c_170, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_155, c_161])).
% 1.91/1.16  tff(c_174, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_170])).
% 1.91/1.16  tff(c_175, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_174])).
% 1.91/1.16  tff(c_191, plain, (![B_53, A_54]: (~v1_subset_1(B_53, A_54) | v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.91/1.16  tff(c_194, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_175, c_191])).
% 1.91/1.16  tff(c_200, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_156, c_194])).
% 1.91/1.16  tff(c_201, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_200])).
% 1.91/1.16  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.16  tff(c_205, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_4])).
% 1.91/1.16  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_205])).
% 1.91/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.16  
% 1.91/1.16  Inference rules
% 1.91/1.16  ----------------------
% 1.91/1.16  #Ref     : 0
% 1.91/1.16  #Sup     : 36
% 1.91/1.16  #Fact    : 0
% 1.91/1.16  #Define  : 0
% 1.91/1.16  #Split   : 1
% 1.91/1.16  #Chain   : 0
% 1.91/1.16  #Close   : 0
% 1.91/1.16  
% 1.91/1.16  Ordering : KBO
% 1.91/1.16  
% 1.91/1.16  Simplification rules
% 1.91/1.16  ----------------------
% 1.91/1.16  #Subsume      : 1
% 1.91/1.16  #Demod        : 8
% 1.91/1.16  #Tautology    : 25
% 1.91/1.16  #SimpNegUnit  : 6
% 1.91/1.16  #BackRed      : 2
% 1.91/1.16  
% 1.91/1.16  #Partial instantiations: 0
% 1.91/1.16  #Strategies tried      : 1
% 1.91/1.16  
% 1.91/1.16  Timing (in seconds)
% 1.91/1.16  ----------------------
% 1.91/1.17  Preprocessing        : 0.33
% 1.91/1.17  Parsing              : 0.18
% 1.91/1.17  CNF conversion       : 0.02
% 1.91/1.17  Main loop            : 0.14
% 1.91/1.17  Inferencing          : 0.05
% 1.91/1.17  Reduction            : 0.05
% 1.91/1.17  Demodulation         : 0.03
% 1.91/1.17  BG Simplification    : 0.01
% 1.91/1.17  Subsumption          : 0.02
% 1.91/1.17  Abstraction          : 0.01
% 1.91/1.17  MUC search           : 0.00
% 1.91/1.17  Cooper               : 0.00
% 1.91/1.17  Total                : 0.50
% 1.91/1.17  Index Insertion      : 0.00
% 1.91/1.17  Index Deletion       : 0.00
% 1.91/1.17  Index Matching       : 0.00
% 1.91/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
