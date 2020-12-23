%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 125 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_263,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k2_relat_1(A_74),k2_relat_1(B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_13,B_14)),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_40,B_14,A_13] :
      ( r1_tarski(A_40,B_14)
      | ~ r1_tarski(A_40,k2_relat_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_273,plain,(
    ! [A_74,B_14,A_13] :
      ( r1_tarski(k2_relat_1(A_74),B_14)
      | ~ r1_tarski(A_74,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_263,c_77])).

tff(c_293,plain,(
    ! [A_78,B_79,A_80] :
      ( r1_tarski(k2_relat_1(A_78),B_79)
      | ~ r1_tarski(A_78,k2_zfmisc_1(A_80,B_79))
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_273])).

tff(c_302,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_293])).

tff(c_311,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_302])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_3')
      | ~ r1_tarski(A_40,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_327,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_78])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k8_relat_1(A_11,B_12) = B_12
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_337,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_12])).

tff(c_346,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_337])).

tff(c_376,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k6_relset_1(A_82,B_83,C_84,D_85) = k8_relat_1(C_84,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_383,plain,(
    ! [C_84] : k6_relset_1('#skF_1','#skF_2',C_84,'#skF_4') = k8_relat_1(C_84,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_376])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_440,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_24])).

tff(c_441,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_440])).

tff(c_472,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( r2_relset_1(A_91,B_92,C_93,C_93)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_510,plain,(
    ! [C_97] :
      ( r2_relset_1('#skF_1','#skF_2',C_97,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_472])).

tff(c_515,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_510])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.39  
% 2.62/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.62/1.40  
% 2.62/1.40  %Foreground sorts:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Background operators:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Foreground operators:
% 2.62/1.40  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.62/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.40  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.40  
% 2.62/1.41  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.62/1.41  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.62/1.41  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.62/1.41  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.62/1.41  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.62/1.41  tff(f_52, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 2.62/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.62/1.41  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.62/1.41  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.62/1.41  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.62/1.41  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.62/1.41  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.41  tff(c_41, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.41  tff(c_47, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.62/1.41  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_47])).
% 2.62/1.41  tff(c_32, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.41  tff(c_40, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.62/1.41  tff(c_263, plain, (![A_74, B_75]: (r1_tarski(k2_relat_1(A_74), k2_relat_1(B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.41  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_13, B_14)), B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.41  tff(c_69, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.41  tff(c_77, plain, (![A_40, B_14, A_13]: (r1_tarski(A_40, B_14) | ~r1_tarski(A_40, k2_relat_1(k2_zfmisc_1(A_13, B_14))))), inference(resolution, [status(thm)], [c_14, c_69])).
% 2.62/1.41  tff(c_273, plain, (![A_74, B_14, A_13]: (r1_tarski(k2_relat_1(A_74), B_14) | ~r1_tarski(A_74, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_263, c_77])).
% 2.62/1.41  tff(c_293, plain, (![A_78, B_79, A_80]: (r1_tarski(k2_relat_1(A_78), B_79) | ~r1_tarski(A_78, k2_zfmisc_1(A_80, B_79)) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_273])).
% 2.62/1.41  tff(c_302, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_293])).
% 2.62/1.41  tff(c_311, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_302])).
% 2.62/1.41  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.41  tff(c_78, plain, (![A_40]: (r1_tarski(A_40, '#skF_3') | ~r1_tarski(A_40, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_69])).
% 2.62/1.41  tff(c_327, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_311, c_78])).
% 2.62/1.41  tff(c_12, plain, (![A_11, B_12]: (k8_relat_1(A_11, B_12)=B_12 | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.62/1.41  tff(c_337, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_327, c_12])).
% 2.62/1.41  tff(c_346, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_337])).
% 2.62/1.41  tff(c_376, plain, (![A_82, B_83, C_84, D_85]: (k6_relset_1(A_82, B_83, C_84, D_85)=k8_relat_1(C_84, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.41  tff(c_383, plain, (![C_84]: (k6_relset_1('#skF_1', '#skF_2', C_84, '#skF_4')=k8_relat_1(C_84, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_376])).
% 2.62/1.41  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.41  tff(c_440, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_24])).
% 2.62/1.41  tff(c_441, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_440])).
% 2.62/1.41  tff(c_472, plain, (![A_91, B_92, C_93, D_94]: (r2_relset_1(A_91, B_92, C_93, C_93) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.41  tff(c_510, plain, (![C_97]: (r2_relset_1('#skF_1', '#skF_2', C_97, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_28, c_472])).
% 2.62/1.41  tff(c_515, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_510])).
% 2.62/1.41  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_515])).
% 2.62/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.41  
% 2.62/1.41  Inference rules
% 2.62/1.41  ----------------------
% 2.62/1.41  #Ref     : 0
% 2.62/1.41  #Sup     : 107
% 2.62/1.41  #Fact    : 0
% 2.62/1.41  #Define  : 0
% 2.62/1.41  #Split   : 4
% 2.62/1.41  #Chain   : 0
% 2.62/1.41  #Close   : 0
% 2.62/1.41  
% 2.62/1.41  Ordering : KBO
% 2.62/1.41  
% 2.62/1.41  Simplification rules
% 2.62/1.41  ----------------------
% 2.62/1.41  #Subsume      : 14
% 2.62/1.41  #Demod        : 26
% 2.62/1.41  #Tautology    : 15
% 2.62/1.41  #SimpNegUnit  : 1
% 2.62/1.41  #BackRed      : 1
% 2.62/1.41  
% 2.62/1.41  #Partial instantiations: 0
% 2.62/1.41  #Strategies tried      : 1
% 2.62/1.41  
% 2.62/1.41  Timing (in seconds)
% 2.62/1.41  ----------------------
% 2.62/1.41  Preprocessing        : 0.30
% 2.62/1.41  Parsing              : 0.16
% 2.62/1.41  CNF conversion       : 0.02
% 2.62/1.41  Main loop            : 0.33
% 2.62/1.42  Inferencing          : 0.12
% 2.62/1.42  Reduction            : 0.11
% 2.62/1.42  Demodulation         : 0.08
% 2.62/1.42  BG Simplification    : 0.01
% 2.62/1.42  Subsumption          : 0.06
% 2.62/1.42  Abstraction          : 0.02
% 2.62/1.42  MUC search           : 0.00
% 2.62/1.42  Cooper               : 0.00
% 2.62/1.42  Total                : 0.67
% 2.62/1.42  Index Insertion      : 0.00
% 2.62/1.42  Index Deletion       : 0.00
% 2.62/1.42  Index Matching       : 0.00
% 2.62/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
