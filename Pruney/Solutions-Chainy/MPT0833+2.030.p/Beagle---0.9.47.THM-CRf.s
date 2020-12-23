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
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 (  95 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_98,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_124,plain,(
    ! [A_55,B_56,C_57] :
      ( m1_subset_1(k2_relset_1(A_55,B_56,C_57),k1_zfmisc_1(B_56))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_124])).

tff(c_142,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_137])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,'#skF_3')
      | ~ r1_tarski(A_37,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_168,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_67])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k8_relat_1(A_11,B_12) = B_12
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_179,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_188,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_179])).

tff(c_197,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k6_relset_1(A_59,B_60,C_61,D_62) = k8_relat_1(C_61,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_208,plain,(
    ! [C_61] : k6_relset_1('#skF_1','#skF_2',C_61,'#skF_4') = k8_relat_1(C_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_197])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_210,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_22])).

tff(c_211,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_210])).

tff(c_303,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( r2_relset_1(A_75,B_76,C_77,C_77)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_315,plain,(
    ! [C_79] :
      ( r2_relset_1('#skF_1','#skF_2',C_79,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_303])).

tff(c_323,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_315])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:13:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.37  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.43/1.37  
% 2.43/1.37  %Foreground sorts:
% 2.43/1.37  
% 2.43/1.37  
% 2.43/1.37  %Background operators:
% 2.43/1.37  
% 2.43/1.37  
% 2.43/1.37  %Foreground operators:
% 2.43/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.43/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.43/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.37  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.43/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.37  
% 2.43/1.38  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.43/1.38  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.43/1.38  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.43/1.38  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.43/1.38  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.43/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.43/1.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.43/1.38  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.43/1.38  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.43/1.38  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.43/1.38  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.38  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.38  tff(c_38, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.43/1.38  tff(c_44, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_38])).
% 2.43/1.38  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 2.43/1.38  tff(c_98, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.38  tff(c_107, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_98])).
% 2.43/1.38  tff(c_124, plain, (![A_55, B_56, C_57]: (m1_subset_1(k2_relset_1(A_55, B_56, C_57), k1_zfmisc_1(B_56)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.38  tff(c_137, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_124])).
% 2.43/1.38  tff(c_142, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_137])).
% 2.43/1.38  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.38  tff(c_150, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_142, c_4])).
% 2.43/1.38  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.38  tff(c_61, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.38  tff(c_67, plain, (![A_37]: (r1_tarski(A_37, '#skF_3') | ~r1_tarski(A_37, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.43/1.38  tff(c_168, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_150, c_67])).
% 2.43/1.38  tff(c_12, plain, (![A_11, B_12]: (k8_relat_1(A_11, B_12)=B_12 | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.38  tff(c_179, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_168, c_12])).
% 2.43/1.38  tff(c_188, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_179])).
% 2.43/1.38  tff(c_197, plain, (![A_59, B_60, C_61, D_62]: (k6_relset_1(A_59, B_60, C_61, D_62)=k8_relat_1(C_61, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.38  tff(c_208, plain, (![C_61]: (k6_relset_1('#skF_1', '#skF_2', C_61, '#skF_4')=k8_relat_1(C_61, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_197])).
% 2.43/1.38  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.38  tff(c_210, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_22])).
% 2.43/1.38  tff(c_211, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_210])).
% 2.43/1.38  tff(c_303, plain, (![A_75, B_76, C_77, D_78]: (r2_relset_1(A_75, B_76, C_77, C_77) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.43/1.38  tff(c_315, plain, (![C_79]: (r2_relset_1('#skF_1', '#skF_2', C_79, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_26, c_303])).
% 2.43/1.38  tff(c_323, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_315])).
% 2.43/1.38  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_323])).
% 2.43/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  Inference rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Ref     : 0
% 2.43/1.38  #Sup     : 68
% 2.43/1.38  #Fact    : 0
% 2.43/1.38  #Define  : 0
% 2.43/1.38  #Split   : 4
% 2.43/1.38  #Chain   : 0
% 2.43/1.38  #Close   : 0
% 2.43/1.38  
% 2.43/1.38  Ordering : KBO
% 2.43/1.38  
% 2.43/1.38  Simplification rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Subsume      : 6
% 2.43/1.38  #Demod        : 17
% 2.43/1.38  #Tautology    : 15
% 2.43/1.38  #SimpNegUnit  : 1
% 2.43/1.38  #BackRed      : 1
% 2.43/1.38  
% 2.43/1.38  #Partial instantiations: 0
% 2.43/1.38  #Strategies tried      : 1
% 2.43/1.38  
% 2.43/1.38  Timing (in seconds)
% 2.43/1.38  ----------------------
% 2.43/1.38  Preprocessing        : 0.30
% 2.43/1.38  Parsing              : 0.17
% 2.43/1.38  CNF conversion       : 0.02
% 2.43/1.38  Main loop            : 0.25
% 2.43/1.38  Inferencing          : 0.10
% 2.43/1.38  Reduction            : 0.07
% 2.43/1.38  Demodulation         : 0.05
% 2.43/1.38  BG Simplification    : 0.01
% 2.43/1.38  Subsumption          : 0.05
% 2.43/1.38  Abstraction          : 0.02
% 2.43/1.38  MUC search           : 0.00
% 2.43/1.38  Cooper               : 0.00
% 2.43/1.38  Total                : 0.58
% 2.43/1.38  Index Insertion      : 0.00
% 2.43/1.38  Index Deletion       : 0.00
% 2.43/1.38  Index Matching       : 0.00
% 2.43/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
